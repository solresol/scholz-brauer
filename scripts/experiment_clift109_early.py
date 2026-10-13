#!/usr/bin/env python3
"""Exhaust the six arbitrary early bases of the selected Clift109 graph.

Fix only the seed, terminal, and Mersenne bases at 23,28,51,58. The Lean
small-complement theorem forces B5=31*2^k (k<19), B7=127*2^l (l<17).
Reuse the complete complement/production enumerator for 2,4,8,15. This is
an exact computational exclusion; the cost minimum is not a Lean theorem.
"""
import argparse
from collections import Counter
from datetime import datetime
import hashlib
import itertools
import json
from pathlib import Path
import platform
import time
from zoneinfo import ZoneInfo

from experiment_clift109_neighborhood import (
    ROOT, SOURCE, PARENTS, mersenne, base_assignments, pairs_cached,
    brute_pairs, caps_for, check_allocation, require,
)

FREE = (2, 4, 5, 7, 8, 15)


def nonblock_vertices(bases):
    return [v for v, value in zip(SOURCE, bases)
            if value // (value & -value) != mersenne(v)]


def experiment():
    start = time.perf_counter()
    started = datetime.now(ZoneInfo('Australia/Sydney')).isoformat()
    provenance = json.loads((ROOT / 'data/2026-10-08-clift109-source.json').read_text())
    require(provenance['source'] == SOURCE and provenance['selected_parents'] ==
            [list(pair) for pair in PARENTS], 'primary graph transcription differs')
    require(hashlib.sha256((ROOT / 'data/2026-10-08-clift109.png').read_bytes()).hexdigest()
            == provenance['diagram_sha256'], 'primary diagram hash differs')
    require(all(SOURCE[p] + SOURCE[q] == SOURCE[i]
                for i, (p, q) in enumerate(PARENTS, 1)), 'invalid graph')
    counts = {'candidate_branches': 0, 'production_fallbacks': 0}
    histogram = Counter()
    shapes = Counter()
    viable = 0
    best = None
    minima = []
    base_hash = hashlib.sha256()
    # Every early base is <M23. The repeated consumption equations at 28 and
    # 58 and small_mersenne_complement prove these complete shift ranges.
    # There is no carry-free assumption in that Lean reduction.
    for k, l in itertools.product(range(19), range(17)):
        bases = [None if v in FREE else mersenne(v) for v in SOURCE]
        bases[SOURCE.index(5)] = 31 << k
        bases[SOURCE.index(7)] = 127 << l
        for row in base_assignments(bases, counts):
            viable += 1
            require([bin(v).count('1') for v in row] == SOURCE, 'wrong bit counts')
            shapes[tuple(nonblock_vertices(row))] += 1
            base_hash.update((json.dumps(row, separators=(',', ':')) + '\n').encode())
            options = [pairs_cached(row[p], row[q], row[i])
                       for i, (p, q) in enumerate(PARENTS, 1)]
            for labels in itertools.product(*options):
                caps = caps_for(labels)
                cost = sum(caps)
                histogram[cost] += 1
                if best is None or cost < best:
                    best, minima = cost, []
                if cost == best:
                    minima.append({'bases': row, 'labels': labels, 'caps': caps})
    require(best == 110, 'six-early-base minimum changed')
    checked_rows = set()
    certificates = {}
    for row in minima:
        key = tuple(row['bases'])
        if key not in checked_rows:
            checked_rows.add(key)
            for i, (p, q) in enumerate(PARENTS, 1):
                require(pairs_cached(key[p], key[q], key[i]) ==
                        brute_pairs(key[p], key[q], key[i]), 'independent shifts differ')
        independent_caps = [max([0] + [label[side]
                            for parents, label in zip(PARENTS, row['labels'])
                            for side in (0, 1) if parents[side] == i])
                            for i in range(len(SOURCE))]
        require(row['caps'] == independent_caps, 'independent cap sum differs')
        document = check_allocation(row['bases'], row['labels'])
        shape = ','.join(map(str, nonblock_vertices(row['bases']))) or 'all-blocks'
        certificates.setdefault(shape, document)
    return {
        'started_at_australia_sydney': started, 'python': platform.python_version(),
        'seed': None, 'arithmetic': 'exact Python integers; exhaustive finite search',
        'source': SOURCE, 'selected_parents': PARENTS,
        'free_vertices': FREE, 'fixed_tail_vertices': [23, 28, 51, 58],
        'reduction_theorem': 'ScholzBrauer.Clift109.early_detours_rigid',
        'shift_ranges': {'B5=31*2^k': [0, 18], 'B7=127*2^l': [0, 16]},
        'reduced_pairs': 19 * 17, **counts, 'viable_base_assignments': viable,
        'base_enumeration_sha256': base_hash.hexdigest(),
        'nonblock_vertex_patterns': [{'vertices': v, 'base_assignments': count}
                                    for v, count in sorted(shapes.items())],
        'labellings_modulo_parallel_swap': sum(histogram.values()),
        'cost_histogram': dict(sorted(histogram.items())),
        'minimum_doublings': best, 'minimum_additions': best + 11,
        'minimizers': minima, 'independently_replayed_minimizers': len(minima),
        'distinct_minimizing_base_assignments': len(checked_rows),
        'one_minimum_certificate_per_nonblock_pattern': certificates,
        'runtime_seconds': round(time.perf_counter() - start, 6),
        'claim_boundary': 'No budget-108 labelling with only the six early bases '
            'free. The general complement and finite reduction are Lean theorems; '
            'the complete enumeration and minimum 110 remain computational. '
            'Independent replay checks witnesses, not enumeration completeness. '
            'No arbitrary-graph exclusion, source/Mersenne optimum, new Scholz '
            'instance, or novelty is claimed.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = experiment()
    if args.output:
        with args.output.open('x') as handle:
            json.dump(report, handle, indent=2)
            handle.write('\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
