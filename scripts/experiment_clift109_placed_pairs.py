#!/usr/bin/env python3
"""Refine the 344-pair necessary domain using actual exception positions.

Two exhaustive algorithms compute all singleton positions: C++ arithmetic-run
peeling, and independent Python divisibility by 1+2^m. A third small-domain
matching recurrence and direct set replay check the implementations. Neither
program nor its finite result is a Lean proof of enumeration completeness.
"""
import argparse
from collections import defaultdict
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import platform
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SPARSE = ROOT / 'results/2026-11-05-sparse-residue-pairs.json'
SAVED = ROOT / 'results/2026-10-18-clift109-box-exclusion.json'
CPP = ROOT / 'scripts/clift109_placed_pairs.cpp'


def positions(mask, n):
    return [s for s in range(n) if mask & (1 << s)]


def replay(n, m, d, s, starts):
    """Direct set deletion and least-element matching, without bit arithmetic."""
    if not (0 < m < n and 0 < d < n and 0 <= s < n):
        raise ValueError('invalid bound, step or singleton')
    if len(starts) != 3:
        raise ValueError('expected three opposite-step pairs')
    exceptions = [s] + [v for x in starts for v in (x, x + d)]
    if len(set(exceptions)) != 7 or any(v < 0 or v >= n for v in exceptions):
        raise ValueError('exception positions overlap or leave the interval')
    remaining = set(range(n)) - set(exceptions)
    half = []
    while remaining:
        x = min(remaining)
        if x + m not in remaining:
            raise ValueError('complement cannot be tiled by the tested step')
        remaining.remove(x)
        remaining.remove(x + m)
        half.append(x)
    if len(half) != (n - 7) // 2:
        raise ValueError('wrong number of regular pairs')
    return half


def cpp_domains(binary, n, pairs):
    proc = subprocess.run([str(binary), str(n)], text=True, check=True,
                          input=''.join(f'{m} {d}\n' for m, d in pairs),
                          stdout=subprocess.PIPE, timeout=60)
    records = {}
    for line in proc.stdout.splitlines():
        tag, *values = line.split()
        if tag == 'D':
            m, d, lo, hi, triples = map(int, values)
            if (m, d) in records:
                raise ValueError('duplicate decision')
            records[m, d] = {'mask': lo + (hi << 64), 'triples': triples,
                             'witnesses': {}}
        elif tag == 'W':
            m, d, s, x, y, z = map(int, values)
            row = records[m, d]
            if s in row['witnesses']:
                raise ValueError('duplicate singleton witness')
            replay(n, m, d, s, (x, y, z))
            row['witnesses'][s] = [x, y, z]
        else:
            raise ValueError('unknown C++ output')
    if list(records) != pairs:
        raise ValueError('incomplete or reordered input coverage')
    for row in records.values():
        if row['mask'] >> n or set(row['witnesses']) != set(positions(row['mask'], n)):
            raise ValueError('singleton decisions and witnesses disagree')
    return records


def division_domain(n, m, d):
    """Independent full enumeration by exact integer division, without runs.

    A disjoint paired support is the binary integer H*(1+2^m). For each
    triple, modular lookup tests all possible singleton positions; a quotient
    is accepted only after checking disjointness and exact reconstruction.
    No parity filter or C++ decision is used to omit a candidate.
    """
    divisor = (1 << m) + 1
    full = (1 << n) - 1
    residues = defaultdict(list)
    for s in range(n):
        bit = 1 << s
        residues[bit % divisor].append(bit)
    edges = [(1 << x) + (1 << (x + d)) for x in range(n - d)]
    found = 0
    triples = 0
    for i, a in enumerate(edges):
        for j in range(i + 1, len(edges)):
            b = edges[j]
            if a & b:
                continue
            ab = a + b
            for k in range(j + 1, len(edges)):
                c = edges[k]
                if ab & c:
                    continue
                triples += 1
                residual = full - ab - c
                for bit in residues.get(residual % divisor, ()):
                    if found & bit or not residual & bit:
                        continue
                    half = (residual - bit) // divisor
                    if not half & (half << m) and half + (half << m) == residual - bit:
                        found |= bit
    return found, triples


def matching_domain(n, m, d):
    """Small independent oracle: branch on partners of the least free point."""
    found = 0
    for s in range(n):
        @lru_cache(None)
        def match(free, used_d):
            if not free:
                return used_d == 3
            if used_d > 3:
                return False
            bit = free & -free
            x = bit.bit_length() - 1
            for step, extra in ((m, 0), (d, 1)):
                y = x + step
                if y < n and free & (1 << y) and match(free ^ bit ^ (1 << y), used_d + extra):
                    return True
            return False
        if match(((1 << n) - 1) ^ (1 << s), 0):
            found |= 1 << s
    return found


def controls(binary, records):
    small = 0
    for n in (7, 9, 11, 13):
        pairs = [(m, d) for m in range(1, n) for d in range(1, n)]
        rows = cpp_domains(binary, n, pairs)
        for (m, d), row in rows.items():
            mask, triples = division_domain(n, m, d)
            if row['mask'] != mask or row['triples'] != triples or mask != matching_domain(n, m, d):
                raise ValueError(f'small matching oracle disagrees at {(n, m, d)}')
            small += 1
    negative = 0
    (m, d), row = next((p, r) for p, r in records.items() if r['witnesses'])
    s, starts = next(iter(row['witnesses'].items()))
    x, y, z = starts
    for point, triple in ((s, [x, x, z]), (x, starts), (s, [-1, y, z]),
                          (s, [109 - d, y, z])):
        try:
            replay(109, m, d, point, triple)
        except ValueError:
            negative += 1
        else:
            raise ValueError('corrupt placement accepted')
    configs = json.loads(SAVED.read_text())['configurations']
    for cfg in configs:
        u, v, _, d1, d2, _, _, p, q, A1, A2, A3 = cfg
        s = A3 + p
        for m, d, starts in ((u, d1, [A3, A3 + d2, A3 + q]),
                              (d1, u, [A1 + p, A1 + p + v, A2 + p])):
            replay(109, m, d, s, starts)
            if not records[m, d]['mask'] & (1 << s):
                raise ValueError('saved interval configuration lost')
    return {'small_complete_matching_cases': small,
            'corrupt_placements_rejected': negative,
            'saved_configurations': len(configs),
            'saved_actual_placements': 2 * len(configs)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('refusing to replace an existing report')
    signal.alarm(180)
    started = time.monotonic()
    timestamp = datetime.now(timezone.utc).isoformat()
    pairs = [tuple(p) for p in json.loads(SPARSE.read_text())['surviving_pairs']]
    if len(set(pairs)) != 344 or set(pairs) != {p[::-1] for p in pairs}:
        raise ValueError('unexpected input domain')
    timings = {}
    with tempfile.TemporaryDirectory(prefix='clift109-placed-') as temp:
        binary = Path(temp) / 'placed-pairs'
        command = ['g++', '-O3', '-std=c++17', '-Wall', '-Wextra', '-Werror', str(CPP), '-o', str(binary)]
        subprocess.run(command, check=True, timeout=30)
        t = time.monotonic()
        records = cpp_domains(binary, 109, pairs)
        timings['cpp_seconds'] = time.monotonic() - t
        t = time.monotonic()
        for (m, d), row in records.items():
            mask, triples = division_domain(109, m, d)
            if row['mask'] != mask or row['triples'] != triples:
                raise ValueError(f'independent full enumeration disagrees at {(m, d)}')
        timings['python_division_seconds'] = time.monotonic() - t
        t = time.monotonic()
        checks = controls(binary, records)
        timings['controls_seconds'] = time.monotonic() - t
    survivors = [p for p in pairs if records[p]['mask'] & records[p[::-1]]['mask']]
    directional_rejections = [p for p in pairs if not records[p]['mask']]
    shared_only = [p for p in pairs if records[p]['mask'] and records[p[::-1]]['mask']
                   and not records[p]['mask'] & records[p[::-1]]['mask']]
    if len(survivors) != 278 or len(directional_rejections) != 34 or len(shared_only) != 14:
        raise ValueError('unexpected refinement; inspect before publishing')
    paths = [Path(__file__), CPP, SPARSE, SAVED,
             ROOT / 'lean/ScholzBrauer/Clift109PlacedPairs.lean',
             ROOT / 'lean/ScholzBrauer/Clift109SparseDomain.lean']
    report = {
        'started_at_utc': timestamp,
        'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'python': platform.python_version(),
        'compiler': subprocess.check_output(['g++', '--version'], text=True).splitlines()[0],
        'compile_argv': command, 'dependencies': 'Python standard library; installed g++',
        'random_seed': None, 'timeout_seconds': 180, 'cpp_timeout_seconds': 60,
        'bounds': {'interval': [0, 108], 'input_ordered_pairs': 344,
                   'pair_starts': '0 <= x < y < z < 109-d; six endpoints distinct',
                   'singleton': '0 <= s < 109; distinct from the six endpoints',
                   'regular_pairs': 51, 'opposite_step_pairs': 3},
        'algorithms': ['all triples; arithmetic-run peeling and singleton deletion',
                       'all triples; independent integer divisibility and disjoint quotient'],
        'disjoint_triples_checked_per_algorithm': sum(r['triples'] for r in records.values()),
        'directional_rejections': directional_rejections,
        'pairs_removed_by_either_empty_direction': 344 - sum(bool(records[p]['mask'] and records[p[::-1]]['mask']) for p in pairs),
        'additional_shared_singleton_rejections': shared_only,
        'surviving_pair_count': len(survivors), 'removed_pair_count': 344 - len(survivors),
        'surviving_pairs': survivors,
        'two_three_shared_singletons': positions(records[2, 3]['mask'] & records[3, 2]['mask'], 109),
        'decisions': [{'modulus': m, 'opposite_step': d,
                       'singleton_positions': positions(r['mask'], 109),
                       'disjoint_triples': r['triples'],
                       'witnesses': [{'singleton': s, 'starts': xyz} for s, xyz in r['witnesses'].items()]}
                      for (m, d), r in records.items()],
        'controls': checks, 'timings': timings,
        'elapsed_seconds': time.monotonic() - started,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'claim_boundary': ('Exact computational necessary refinement from 344 to 278 ordered pairs. '
                           'The placed-pair implication is proved in Lean; the finite enumeration '
                           'and 278 count are not kernel checked. Opposite directions share only '
                           'the singleton in this test; their other coordinates and halves need '
                           'not agree. No box/cap feasibility, min(u,d1)=1, selected-109 exclusion '
                           'or new Scholz theorem follows.'),
    }
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    signal.alarm(0)
    print(json.dumps({key: report[key] for key in ('surviving_pair_count', 'removed_pair_count',
                                                 'disjoint_triples_checked_per_algorithm',
                                                 'controls', 'timings', 'elapsed_seconds')}))


if __name__ == '__main__':
    main()
