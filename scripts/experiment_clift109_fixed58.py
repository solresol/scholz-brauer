#!/usr/bin/env python3
"""Exact budget-108 exclusion with only B58=M58 and endpoints fixed.

Use the Lean fixed58_tail_rigid domain (51 pairs), the existing complete
base enumerator, and two repeated-consumer equations to avoid large forward
branches. Checkpoint each completed pair; an interrupted pair proves nothing.
The exclusion is computational, not a kernel-checked minimum theorem.
"""
import argparse
from datetime import datetime
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import platform
import signal
import time
from zoneinfo import ZoneInfo

from experiment_clift109_neighborhood import (
    ROOT, SOURCE, PARENTS, mersenne, base_assignments, pairs_cached,
    consumption_domain, parallel_domain, production_domain,
    brute_pairs, caps_for, check_allocation, require,
)


@lru_cache(None)
def repeated_domain(target, known, bits):
    """Necessary complete domain for u*2^A+u*2^B+known*2^C=target.

    All three terms are disjoint; A!=B. Exchange A,B and factor the lower
    shift: target-known*2^C = u*2^min(A,B)*(1+2^abs(A-B)). Enumerate C and
    the positive difference, divide exactly, then remove each power of two.
    The result is an overapproximation until the original equations are checked.
    """
    values = set()
    for c in range(target.bit_length()):
        remainder = target - (known << c)
        if remainder <= 0:
            break
        for d in range(1, remainder.bit_length()):
            divisor = 1 + (1 << d)
            if remainder % divisor:
                continue
            u = remainder // divisor
            if u & (u << d) or bin(u).count('1') != bits:
                continue
            while True:
                values.add(u)
                if u & 1:
                    break
                u //= 2
    return frozenset(values)


def repeated_consumers(bases):
    domains = {}
    # B51 = B23*(2^(a28+a51)+2^b51) + B5*2^(b28+a51).
    if bases[7] is None and bases[9] is not None and bases[3] is not None:
        domains[7] = repeated_domain(bases[9], bases[3], 23)
    # B23 = B8*(2^(a15+a23)+2^b23) + B7*2^(b15+a23).
    if bases[5] is None and bases[7] is not None and bases[4] is not None:
        domains[5] = repeated_domain(bases[7], bases[4], 8)
    return domains


def budget_labels(options, budget, counts):
    """Exact feasibility, pruning only mandatory per-vertex outgoing caps."""
    suffix = [[0] * len(SOURCE) for _ in range(len(PARENTS) + 1)]
    for i in reversed(range(len(PARENTS))):
        suffix[i] = suffix[i + 1].copy()
        for side, p in enumerate(PARENTS[i]):
            suffix[i][p] = max(suffix[i][p], min(pair[side] for pair in options[i]))

    def visit(i, caps, labels):
        counts['cost_states'] += 1
        if sum(max(c, m) for c, m in zip(caps, suffix[i])) > budget:
            return None
        if i == len(PARENTS):
            return labels
        p, q = PARENTS[i]
        for a, b in options[i]:
            updated = caps.copy()
            updated[p] = max(updated[p], a)
            updated[q] = max(updated[q], b)
            result = visit(i + 1, updated, labels + [(a, b)])
            if result is not None:
                return result
        return None

    return visit(0, [0] * len(SOURCE), [])


def check_repeated_domain():
    # Independent finite oracle for the new arithmetic pruning, not a re-run
    # of the earlier chain experiments. Test every u,A,B,C directly.
    checked = 0
    for target in range(1, 64):
        for known in range(1, 8):
            expected = {bits: set() for bits in range(1, 6)}
            for u in range(1, target):
                bits = bin(u).count('1')
                if bits not in expected:
                    continue
                for a, b in itertools.combinations(range(target.bit_length()), 2):
                    x, y = u << a, u << b
                    if x & y or x + y >= target:
                        continue
                    for c in range(target.bit_length()):
                        z = known << c
                        if x + y + z == target and not ((x | y) & z):
                            expected[bits].add(u)
            for bits, values in expected.items():
                actual = repeated_domain(target, known, bits)
                # Production can relax disjointness with the known term; it
                # may admit extra values, but must not lose a valid one.
                require(values <= actual, 'repeated-consumer domain omitted a base')
                checked += 1
    repeated_domain.cache_clear()
    return checked


def run_case(k, l):
    start = time.perf_counter()
    bases = [None] * len(SOURCE)
    for v, value in [(1, 1), (7, mersenne(7) << l), (51, mersenne(51) << k),
                     (58, mersenne(58)), (109, mersenne(109))]:
        bases[SOURCE.index(v)] = value
    counts = {'candidate_branches': 0, 'production_fallbacks': 0, 'cost_states': 0}
    viable = 0
    digest = hashlib.sha256()
    witness = None
    for row in base_assignments(bases, counts, repeated_consumers):
        viable += 1
        require([bin(v).count('1') for v in row] == SOURCE, 'wrong bit counts')
        digest.update((json.dumps(row, separators=(',', ':')) + '\n').encode())
        options = [pairs_cached(row[p], row[q], row[i])
                   for i, (p, q) in enumerate(PARENTS, 1)]
        labels = budget_labels(options, 108, counts)
        require(labels is None, 'budget-108 witness found; inspect before claiming exclusion')
        if witness is None:
            labels = budget_labels(options, 109, counts)
            if labels is not None:
                for i, (p, q) in enumerate(PARENTS, 1):
                    require(options[i-1] == brute_pairs(row[p], row[q], row[i]),
                            'independent local shift enumeration differs')
                independent = min(sum(caps_for(x)) for x in itertools.product(*options))
                require(independent == 109, 'independent witness cost differs')
                witness = {'bases': row, 'labels': labels, 'caps': caps_for(labels),
                           'certificate': check_allocation(row, labels)}
    result = {'k': k, 'l': l, 'complete': True, **counts,
              'viable_base_assignments': viable, 'base_enumeration_sha256': digest.hexdigest(),
              'budget_108_excluded': True, 'witness_109': witness,
              'runtime_seconds': round(time.perf_counter() - start, 6)}
    for function in (repeated_domain, consumption_domain, parallel_domain,
                     production_domain, pairs_cached):
        function.cache_clear()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--max-seconds', type=int, default=240)
    args = parser.parse_args()
    require(args.max_seconds > 0, 'time budget must be positive')
    # Reserve the fresh output before any computation; never replace prior work.
    with args.output.open('x') as handle:
        handle.write('{}\n')
    start = time.perf_counter()
    provenance = json.loads((ROOT / 'data/2026-10-08-clift109-source.json').read_text())
    require(provenance['source'] == SOURCE and provenance['selected_parents'] ==
            [list(pair) for pair in PARENTS], 'primary graph transcription differs')
    require(hashlib.sha256((ROOT / 'data/2026-10-08-clift109.png').read_bytes()).hexdigest()
            == provenance['diagram_sha256'], 'primary diagram hash differs')
    require(all(SOURCE[p] + SOURCE[q] == SOURCE[i]
                for i, (p, q) in enumerate(PARENTS, 1)), 'invalid graph')
    paths = [Path(__file__), ROOT/'scripts/experiment_clift109_neighborhood.py',
             ROOT/'scripts/experiment_clift109.py', ROOT/'scripts/check_certificate.py',
             ROOT/'lean/ScholzBrauer/MersenneComplement.lean']
    report = {'started_at_australia_sydney': datetime.now(ZoneInfo('Australia/Sydney')).isoformat(),
              'python': platform.python_version(), 'seed': None,
              'arithmetic': 'exact Python integers; exhaustive finite domains',
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in paths},
              'source': SOURCE, 'selected_parents': PARENTS,
              'fixed_vertices': [1, 58, 109], 'free_vertices': SOURCE[1:-2],
              'reduction_theorem': 'ScholzBrauer.Clift109.fixed58_tail_rigid',
              'candidate_pairs': [(0, l) for l in range(44)] + [(k, 0) for k in range(1, 8)],
              'time_limit_seconds': args.max_seconds, 'cases': [], 'complete': False,
              'claim_boundary': 'Computational exclusion of budget 108 with B58=M58. '
              'Independent replay establishes witnesses, not enumeration completeness. '
              'No unrestricted graph exclusion, new Scholz instance, optimal source or '
              'Mersenne chain length, Lean minimum theorem, or novelty claim.'}

    def checkpoint():
        report['runtime_seconds'] = round(time.perf_counter() - start, 6)
        temporary = args.output.with_suffix('.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(args.output)

    def stop(*_):
        raise TimeoutError('bounded experiment time limit reached')

    signal.signal(signal.SIGALRM, stop)
    signal.alarm(args.max_seconds)
    try:
        report['small_domain_oracle_cases'] = check_repeated_domain()
        for k, l in report['candidate_pairs']:
            report['active_pair'] = [k, l]
            checkpoint()
            result = run_case(k, l)
            report['cases'].append(result)
            checkpoint()
            print(json.dumps({key: result[key] for key in
                             ('k', 'l', 'viable_base_assignments', 'runtime_seconds')}), flush=True)
        report['complete'] = True
        report.pop('active_pair', None)
        report['minimum_doublings'] = 109 if any(c['witness_109'] for c in report['cases']) else None
    except TimeoutError as exc:
        report['interruption'] = str(exc)
    finally:
        signal.alarm(0)
        checkpoint()
    print(json.dumps({'complete': report['complete'], 'completed_pairs': len(report['cases']),
                      'runtime_seconds': report['runtime_seconds']}))


if __name__ == '__main__':
    main()
