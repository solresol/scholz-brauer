#!/usr/bin/env python3
"""Exact two-exception labellings of Clift's selected 109 graph.

Keep B_v=2**v-1 except at v=5,7, allowing those two bases and ALL edge shifts
to vary. Exhaust every carry-free labelling in that family; no solver needed.
This does not exclude arbitrary labellings or prove source/Mersenne optimality.
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

from check_certificate import check_document
from hansen_lift import find_underlining
from star_lift import star_lift

ROOT = Path(__file__).resolve().parents[1]
SOURCE = [1, 2, 4, 5, 7, 8, 15, 23, 28, 51, 58, 109]
PARENTS = [(0, 0), (1, 1), (2, 0), (3, 1), (2, 2), (5, 4),
           (6, 5), (7, 3), (8, 7), (9, 4), (10, 9)]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def mersenne(n):
    return (1 << n) - 1


def power_of_two(n):
    return n > 0 and n & (n - 1) == 0


def local_pairs(left, right, target):
    """Every exact disjoint pair; derive the second shift by exact division.

    Any positive shifted term is <=target, so its exponent <target.bit_length().
    Parallel equal-parent edges are interchangeable; retain one orientation.
    """
    pairs = []
    for a in range(target.bit_length()):
        remainder = target - (left << a)
        if remainder <= 0 or remainder % right:
            continue
        quotient = remainder // right
        if not power_of_two(quotient):
            continue
        b = quotient.bit_length() - 1
        if not ((left << a) & (right << b)) and (left != right or a > b):
            pairs.append((a, b))
    return pairs


def brute_pairs(left, right, target):
    """Independent nested shift enumeration, without division or logarithms."""
    pairs = []
    for a in range(target.bit_length()):
        for b in range(target.bit_length()):
            x, y = left << a, right << b
            if x + y == target and not (x & y) and (left != right or a > b):
                pairs.append((a, b))
    return pairs


def consumption_candidates(child, known_parent):
    """Complete positive bases consumed with M(known_parent) to make M(child).

    The known parent's shift is 0..child-known_parent. For each remainder,
    divide by every power of two that divides it exactly, including one.
    No odd-base normalisation is assumed: even exceptional bases are retained.
    """
    values = set()
    for shift in range(child - known_parent + 1):
        remainder = mersenne(child) - (mersenne(known_parent) << shift)
        while True:
            values.add(remainder)
            if remainder & 1:
                break
            remainder //= 2
    return sorted(values)


def forward_base_pairs():
    """Independently produce exceptional bases first, then check consumption.

    B5<=M28 and B7<=M58 follow from their positive outgoing summand equations.
    Hence all four production shifts lie in 0..27 and 0..57 respectively.
    """
    candidates5 = set()
    for a, b in itertools.product(range(28), repeat=2):
        x, y = 15 << a, 1 << b
        v = x + y
        if v <= mersenne(28) and not (x & y) and brute_pairs(v, mersenne(23), mersenne(28)):
            candidates5.add(v)
    pairs = set()
    production_checks = 0
    for v5 in sorted(candidates5):
        for c, d in itertools.product(range(58), repeat=2):
            production_checks += 1
            x, y = v5 << c, 3 << d
            v7 = x + y
            if v7 > mersenne(15) or x & y:
                continue
            # Vertex 7 must also feed M15 alongside the fixed M8.
            if not brute_pairs(255, v7, mersenne(15)):
                continue
            # Enumerate the known-parent shift separately and divide exactly.
            # This consumption check is independent of consumption_candidates.
            for k in range(8):
                remainder = mersenne(58) - (mersenne(51) << k)
                if remainder % v7 == 0 and power_of_two(remainder // v7):
                    pairs.add((v5, v7))
                    break
    return pairs, production_checks


def caps_for(labels):
    caps = [0] * len(SOURCE)
    for (p, q), (a, b) in zip(PARENTS, labels):
        caps[p] = max(caps[p], a)
        caps[q] = max(caps[q], b)
    return caps


def check_allocation(bases, labels):
    """Use the existing independent index replay; no new certificate format."""
    caps = caps_for(labels)
    nodes = {1: None}
    for i, base in enumerate(bases):
        for k in range(caps[i] + 1):
            value = base << k
            if i == k == 0:
                continue
            require(value not in nodes, 'allocated value collision')
            if k:
                pair = (value // 2, value // 2)
            else:
                p, q = PARENTS[i - 1]
                a, b = labels[i - 1]
                pair = (bases[p] << a, bases[q] << b)
            nodes[value] = pair
    values = sorted(nodes)
    index = {v: i for i, v in enumerate(values)}
    document = {'format': 'addition-chain-indices-v1', 'start': 1,
                'target': {'kind': 'mersenne', 'exponent': 109},
                'additions': sum(caps) + 11, 'source_chain': SOURCE,
                'pairs': [[index[a], index[b]] for a, b in
                          (nodes[v] for v in values[1:])]}
    require(check_document(document, exponent=109, additions=sum(caps) + 11) == values,
            'independent allocated replay differs')
    return document


def experiment():
    provenance = json.loads((ROOT / 'data/2026-10-08-clift109-source.json').read_text())
    require(provenance['source'] == SOURCE and provenance['selected_parents'] ==
            [list(pair) for pair in PARENTS], 'source transcription differs')
    image = ROOT / 'data/2026-10-08-clift109.png'
    require(hashlib.sha256(image.read_bytes()).hexdigest() == provenance['diagram_sha256'],
            'primary diagram hash differs')
    alternatives = []
    for i, value in enumerate(SOURCE[1:], 1):
        pairs = [(j, k) for j in range(i) for k in range(j + 1)
                 if SOURCE[j] + SOURCE[k] == value]
        require(PARENTS[i - 1] in pairs, 'invalid selected parents')
        require(len(pairs) == (2 if value == 8 else 1), 'unexpected alternative parents')
        alternatives.append(pairs)
    require(find_underlining(SOURCE) is not None, 'value sequence should be Hansen')
    # The alternate 8=7+1 source is a star chain; independently replay its lift.
    alternate = {'format': 'addition-chain-indices-v1', 'start': 1,
                 'target': {'kind': 'mersenne', 'exponent': 109},
                 'additions': 119, 'source_chain': SOURCE, 'pairs': star_lift(SOURCE)}
    check_document(alternate, exponent=109, additions=119)

    orientation_costs = Counter()
    for bits in itertools.product((False, True), repeat=8):
        choices = iter(bits)
        labels = []
        for p, q in PARENTS:
            labels.append((0, SOURCE[p]) if p != q and next(choices)
                          else (SOURCE[q], 0))
        orientation_costs[sum(caps_for(labels))] += 1
    require(min(orientation_costs) == 110 and orientation_costs[110] == 8,
            'standard orientation minimum differs')

    candidates5 = consumption_candidates(28, 23)
    candidates7 = consumption_candidates(58, 51)
    require((len(candidates5), len(candidates7)) == (28, 58), 'candidate sets changed')
    viable = set()
    histogram = Counter()
    minimizers = []
    best = None
    assignment_count = 0
    for v5, v7 in itertools.product(candidates5, candidates7):
        bases = [mersenne(v) for v in SOURCE]
        bases[3], bases[4] = v5, v7
        options = [local_pairs(bases[p], bases[q], bases[i])
                   for i, (p, q) in enumerate(PARENTS, 1)]
        if not all(options):
            continue
        viable.add((v5, v7))
        require([bin(v).count('1') for v in bases] == SOURCE, 'wrong base bit counts')
        require(options == [brute_pairs(bases[p], bases[q], bases[i])
                            for i, (p, q) in enumerate(PARENTS, 1)],
                'independent local shift enumeration differs')
        for labels in itertools.product(*options):
            assignment_count += 1
            caps = caps_for(labels)
            cost = sum(caps)
            histogram[cost] += 1
            if best is None or cost < best:
                best, minimizers = cost, []
            if cost == best:
                minimizers.append({'bases': bases, 'labels': labels, 'caps': caps})
    forward, checks = forward_base_pairs()
    require(viable == forward, 'forward/backward exceptional-base domains differ')
    require(len(viable) == 63 and assignment_count == 2304, 'enumeration scope changed')
    require(best == 110 and len(minimizers) == 8, 'two-exception minimum differs')
    require(all(v5 in {31 << k for k in range(11)} and
                v7 in {127 << k for k in range(9)} for v5, v7 in viable),
            'structural shifted-Mersenne restriction differs from Lean')
    require(all(row['bases'][3:5] == [31, 127] for row in minimizers),
            'minimum unexpectedly attained at shifted detour bases')
    for row in minimizers:
        row['certificate'] = check_allocation(row['bases'], row['labels'])
    # The old repair's base5=121 is not even a candidate for its later reuse.
    require(121 not in candidates5, 'initial one-gap repair unexpectedly extends')
    return {'source': SOURCE, 'selected_parents': PARENTS,
            'all_source_parents': alternatives,
            'value_sequence_is_star_and_hansen': True,
            'alternate_parent_star_certificate': alternate,
            'fixed_mersenne_vertices': [v for v in SOURCE if v not in (5, 7)],
            'exceptional_bases': {'5': candidates5, '7': candidates7},
            'candidate_base_pairs': len(candidates5) * len(candidates7),
            'viable_base_pairs': sorted(viable),
            'forward_production_checks': checks,
            'standard_orientations': 256,
            'standard_cost_histogram': dict(sorted(orientation_costs.items())),
            'complete_labellings_modulo_parallel_edge_swap': assignment_count,
            'two_exception_cost_histogram': dict(sorted(histogram.items())),
            'minimum_doublings': best, 'required_budget': 108,
            'all_viable_detour_bases_are_shifted_mersennes': True,
            'minimum_labelled_additions': best + 11,
            'minimizers': minimizers,
            'initial_repair_base5': 121, 'initial_repair_reuse_possible': False,
            'claim_boundary': 'Exact exclusion only with every base other than 5 and 7 '
                              'fixed to its Mersenne value. No arbitrary-graph exclusion, '
                              'source optimum, Mersenne optimum, or new Scholz instance.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    begin = time.perf_counter()
    started = datetime.now(ZoneInfo('Australia/Sydney')).isoformat()
    report = experiment()
    report.update({'started_at_australia_sydney': started,
                   'python': platform.python_version(), 'seed': None,
                   'runtime_seconds': round(time.perf_counter() - begin, 6)})
    if args.output:
        with args.output.open('x') as handle:
            json.dump(report, handle, indent=2)
            handle.write('\n')
    print(json.dumps({k: report[k] for k in
                     ['candidate_base_pairs', 'complete_labellings_modulo_parallel_edge_swap',
                      'minimum_doublings', 'required_budget', 'runtime_seconds']}))


if __name__ == '__main__':
    main()
