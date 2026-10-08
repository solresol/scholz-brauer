#!/usr/bin/env python3
"""Exhaust all labellings with at most two extra free bases besides 5 and 7.

The seed is 1, the terminal is M109, and every other base is fixed to its
Mersenne value. Enumerate arbitrary positive free bases and nonnegative shifts,
not just shifted Mersenne bases. Parallel equal-parent swaps are identified.
No solver, floating point, source-optimality or arbitrary-graph exclusion.
"""
import argparse
from collections import Counter
from datetime import datetime
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import platform
import time
from zoneinfo import ZoneInfo

from experiment_clift109 import (
    ROOT, SOURCE, PARENTS, mersenne, local_pairs, brute_pairs,
    caps_for, check_allocation, require,
)

EXTRAS = (2, 4, 8, 15, 23, 28, 51, 58)


@lru_cache(None)
def consumption_domain(target, known):
    """All u>0 satisfying u*2^a + known*2^b=target, without carry pruning.

    Both shifts are <bit_length(target). Repeated exact division enumerates
    every possible a; stop at the odd part. Positive terms bound b as well.
    """
    values = set()
    for b in range(target.bit_length()):
        remainder = target - (known << b)
        if remainder <= 0:
            break
        while True:
            values.add(remainder)
            if remainder & 1:
                break
            remainder //= 2
    return frozenset(values)


@lru_cache(None)
def parallel_domain(target):
    """u*(2^a+2^b)=target; disjoint equal-parent copies require a != b."""
    values = set()
    for a in range(target.bit_length()):
        for b in range(a):
            denominator = (1 << a) + (1 << b)
            if target % denominator == 0:
                values.add(target // denominator)
    return frozenset(values)


@lru_cache(None)
def production_domain(left, right, limit):
    """Complete carry-free production below a proved fixed-descendant bound."""
    return frozenset(x + y
                     for a in range(limit.bit_length())
                     for b in range(limit.bit_length())
                     for x, y in [(left << a, right << b)]
                     if x + y <= limit and not x & y)


pairs_cached = lru_cache(None)(local_pairs)


def base_assignments(bases, counts):
    # All determined equations are checked, including equations that were not
    # used to derive the branching domain. Unknown target values are never
    # silently accepted.
    for i, (p, q) in enumerate(PARENTS, 1):
        if all(bases[k] is not None for k in (i, p, q)):
            if not pairs_cached(bases[p], bases[q], bases[i]):
                return
    if None not in bases:
        yield bases
        return
    domains = {}
    for i, (p, q) in enumerate(PARENTS, 1):
        if bases[i] is None:
            continue
        if p == q and bases[p] is None:
            domain, v = parallel_domain(bases[i]), p
        elif bases[p] is None and bases[q] is not None:
            domain, v = consumption_domain(bases[i], bases[q]), p
        elif bases[q] is None and bases[p] is not None:
            domain, v = consumption_domain(bases[i], bases[p]), q
        else:
            continue
        domains[v] = domains.get(v, domain) & domain
    if not domains:
        # Coupled unknown parents can leave no one-unknown consumption sum.
        # Produce an unknown whose parents are known, using its smallest known
        # descendant as an envelope. Every positive parent is <= its child,
        # since shifts are nonnegative. The fixed terminal guarantees a bound.
        counts['production_fallbacks'] += 1
        for i, (p, q) in enumerate(PARENTS, 1):
            if bases[i] is not None or bases[p] is None or bases[q] is None:
                continue
            reachable = {i}
            for j, (u, v) in enumerate(PARENTS, 1):
                if u in reachable or v in reachable:
                    reachable.add(j)
            limits = [bases[j] for j in reachable if bases[j] is not None]
            require(bool(limits), 'missing fixed descendant')
            domains[i] = production_domain(bases[p], bases[q], min(limits))
    require(bool(domains), 'no complete finite branching domain')
    v, domain = min(domains.items(), key=lambda item: (len(item[1]), item[0]))
    counts['candidate_branches'] += len(domain)
    for value in sorted(domain):
        child = bases.copy()
        child[v] = value
        yield from base_assignments(child, counts)


def run_case(extras):
    start = time.perf_counter()
    free = (5, 7) + extras
    bases = [None if v in free else mersenne(v) for v in SOURCE]
    counts = {'candidate_branches': 0, 'production_fallbacks': 0}
    histogram = Counter()
    viable = 0
    best = None
    minima = []
    base_hash = hashlib.sha256()
    for row in base_assignments(bases, counts):
        viable += 1
        # Bit counts follow inductively from carry-free sums. Check explicitly
        # to catch transcription or incomplete-equation mistakes.
        require([bin(v).count('1') for v in row] == SOURCE, 'wrong bit counts')
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
    require(best == (109 if 28 in extras else 110), 'neighborhood result changed')
    # Independent nested shift enumeration checks every local option at all
    # minimizing base assignments. The index replay checker knows no labelling
    # rules and checks every allocated addition and the exact target/count.
    checked_rows = set()
    for row in minima:
        key = tuple(row['bases'])
        if key not in checked_rows:
            checked_rows.add(key)
            for i, (p, q) in enumerate(PARENTS, 1):
                require(pairs_cached(key[p], key[q], key[i]) ==
                        brute_pairs(key[p], key[q], key[i]),
                        'independent local shifts differ')
        independent_caps = [max([0] + [label[side]
                            for parents, label in zip(PARENTS, row['labels'])
                            for side in (0, 1) if parents[side] == i])
                            for i in range(len(SOURCE))]
        require(row['caps'] == independent_caps, 'independent cost differs')
        document = check_allocation(row['bases'], row['labels'])
        # Keep one full certificate; all minimizers are independently replayed.
        if row is minima[0]:
            certificate = document
    result = {
        'additional_free_vertices': extras, 'free_vertices': sorted(free),
        **counts, 'viable_base_assignments': viable,
        'base_enumeration_sha256': base_hash.hexdigest(),
        'labellings_modulo_parallel_swap': sum(histogram.values()),
        'cost_histogram': dict(sorted(histogram.items())),
        'minimum_doublings': best, 'minimum_additions': best + 11,
        'minimizers': minima, 'independently_replayed_minimizers': len(minima),
        'one_minimum_certificate': certificate,
        'runtime_seconds': round(time.perf_counter() - start, 6),
    }
    # Bound memory across independent cases; no truth is reused across contexts.
    for function in (consumption_domain, parallel_domain, production_domain, pairs_cached):
        function.cache_clear()
    return result


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
    cases = [run_case(extra) for size in (1, 2)
             for extra in itertools.combinations(EXTRAS, size)]
    return {
        'started_at_australia_sydney': started, 'python': platform.python_version(),
        'seed': None, 'arithmetic': 'exact Python integers; exhaustive finite search',
        'source': SOURCE, 'selected_parents': PARENTS,
        'required_doublings': 108, 'cases': cases,
        'completed_cases': len(cases), 'minimum_doublings': min(
            row['minimum_doublings'] for row in cases),
        'runtime_seconds': round(time.perf_counter() - start, 6),
        'claim_boundary': 'Every labelling that changes at most two vertices outside '
            '5 and 7 from their Mersenne bases is excluded at budget 108. This union '
            'includes cases where a free base stays unchanged. The exact search is '
            'not kernel-certified; independent checks validate witnesses, not '
            'enumeration completeness. No full arbitrary-graph exclusion, '
            'source/Mersenne optimum, or new Scholz instance is claimed.',
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
