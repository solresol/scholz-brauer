#!/usr/bin/env python3
"""Evaluate the proved three-pairs-plus-singleton necessary residue tests.

This is a bounded refinement of the 606-pair domain, not an interval search
or a proof of cap feasibility. Two exact algorithms decide the same cyclic
parity equation: exhaustive odd supports of size 1/3, and independent cycle
recurrence with both choices of integration constant on every orbit.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from itertools import combinations
import json
from math import gcd
from pathlib import Path
import platform
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
STEPS = (1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 17, 18, 19, 26, 27, 28, 29,
         51, 52, 53, 54, 55, 56, 57, 58)


def fingerprint(m):
    """Direct multiplicity parity of [0,108], encoded as a residue bit set."""
    bits = 0
    for n in range(109):
        bits ^= 1 << (n % m)
    return bits


def sparse_support(m, d):
    """Every three-element multiset has odd support of size exactly 1 or 3."""
    f = fingerprint(m)
    targets = {f ^ (1 << s): s for s in range(m)}
    edges = [(1 << x) ^ (1 << ((x + d) % m)) for x in range(m)]
    for x, image in enumerate(edges):
        if image in targets:
            return (x, x, x, targets[image])
    for x, y, z in combinations(range(m), 3):
        image = edges[x] ^ edges[y] ^ edges[z]
        if image in targets:
            return (x, y, z, targets[image])
    return None


def cycle_recurrence(m, d):
    """Solve H_i=T_i+T_(i-d) over F2 on all step-d residue cycles.

    On an orbit, choose the first T bit to be zero, propagate, and check
    closure. The only other solution is its complement. A short dynamic
    program keeps all attainable support sizes <=3 across the orbits.
    """
    quotient, remainder = divmod(109, m)
    f = (((1 << m) - 1) if quotient % 2 else 0) ^ ((1 << remainder) - 1)
    if f != fingerprint(m):
        raise ValueError('independent interval formulas disagree')
    unseen, cycles = set(range(m)), []
    while unseen:
        first = min(unseen)
        orbit, x = [], first
        while x in unseen:
            unseen.remove(x)
            orbit.append(x)
            x = (x + d) % m
        if x != first:
            raise ValueError('orbit did not close')
        cycles.append(orbit)
    for singleton in range(m):
        target = f ^ (1 << singleton)
        possible = {0: ()}
        for orbit in cycles:
            value, ones = 0, []
            for x in orbit[1:]:
                value ^= (target >> x) & 1
                if value:
                    ones.append(x)
            if value != ((target >> orbit[0]) & 1):
                possible = {}
                break
            ones = tuple(ones)
            zeros = tuple(x for x in orbit if x not in ones)
            updated = {}
            for count, support in possible.items():
                for option in (ones, zeros):
                    if count + len(option) <= 3:
                        updated[count + len(option)] = support + option
            possible = updated
            if not possible:
                break
        for count in (1, 3):
            if count in possible:
                support = possible[count]
                if count == 1:
                    support *= 3
                return (*support, singleton)
    return None


def check_witness(m, d, witness):
    """Read back seven integer residues, without bit rotations or recurrence."""
    x, y, z, s = witness
    if not all(0 <= v < m for v in witness):
        raise ValueError('residue outside the declared bounds')
    actual = Counter(v % m for v in (x, x+d, y, y+d, z, z+d, s))
    expected = Counter(n % m for n in range(109))
    if {v for v, n in actual.items() if n % 2} != {
            v for v, n in expected.items() if n % 2}:
        raise ValueError('invalid sparse residue witness')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('refusing to replace an existing report')
    # This experiment is deliberately bounded; a timeout establishes no result.
    signal.alarm(60)
    started = time.monotonic()
    timestamp = datetime.now(timezone.utc).isoformat()
    pairs = [(u, d) for u in STEPS for d in STEPS
             if u != d and u+d <= 93 and (54 % gcd(u, d) == 0 or 55 % gcd(u, d) == 0)]
    if len(pairs) != 606:
        raise ValueError('input domain differs from the Lean cardinality')
    records, flags = [], {}
    for m, d in pairs:
        sparse = sparse_support(m, d)
        cycle = cycle_recurrence(m, d)
        if (sparse is None) != (cycle is None):
            raise ValueError(f'algorithms disagree at {(m, d)}')
        for witness in (sparse, cycle):
            if witness is not None:
                check_witness(m, d, witness)
        flags[m, d] = sparse is not None
        records.append({'modulus': m, 'step': d, 'compatible': sparse is not None,
                        'sparse_witness': sparse, 'cycle_witness': cycle})
    survivors = [(u, d) for u, d in pairs if flags[u, d] and flags[d, u]]
    removed = sorted(set(pairs) - set(survivors))
    if len(survivors) != 344 or len(removed) != 262 or (2, 3) not in survivors:
        raise ValueError('unexpected domain refinement')
    paths = ['scripts/experiment_clift109_sparse_residues.py',
             'lean/ScholzBrauer/Clift109SparseResidues.lean',
             'lean/ScholzBrauer/Clift109CommonDivisor.lean',
             'lean/ScholzBrauer/Clift109Residues.lean']
    report = {
        'started_at_utc': timestamp,
        'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                               cwd=ROOT, text=True).strip(),
        'python': platform.python_version(), 'dependencies': 'Python standard library only',
        'random_seed': None, 'timeout_seconds': 60,
        'bounds': {'interval': [0, 108], 'steps': STEPS,
                   'ordered_pair_conditions': 'u != d; u+d <= 93; gcd divides 54 or 55',
                   'each_witness_residue': '0 <= residue < modulus',
                   'exhaustive_support_sizes': [1, 3]},
        'algorithms': ['exhaustive singleton/triple supports',
                       'independent cyclic recurrence and support-size DP'],
        'input_pair_count': len(pairs),
        'one_direction_compatible_count': sum(flags.values()),
        'surviving_pair_count': len(survivors), 'removed_pair_count': len(removed),
        'surviving_pairs': survivors, 'removed_pairs': removed,
        'decisions': records,
        'elapsed_seconds': time.monotonic() - started,
        'input_sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths},
        'claim_boundary': ('Exact computational evaluation of both proved necessary sparse '
                           'residue tests on the 606-pair domain. The 344-pair count is not '
                           'kernel checked. No interval/cap feasibility, min(u,d1)=1, '
                           'selected-109 exclusion, optimality or Scholz theorem follows.'),
    }
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    signal.alarm(0)
    print(json.dumps({k: report[k] for k in ('input_pair_count', 'one_direction_compatible_count',
                                          'surviving_pair_count', 'removed_pair_count',
                                          'elapsed_seconds')}))


if __name__ == '__main__':
    main()
