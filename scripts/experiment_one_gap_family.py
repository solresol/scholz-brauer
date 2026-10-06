#!/usr/bin/env python3
"""Bounded exact checks of the parametric one-gap lift, 2 <= a <= 9, 1 <= b < a.

Compares an explicit replay order with a separately allocated/sorted label graph.
Exhausts source markings, not chains or alternative lift labellings. No seed.
The infinite-family claims are separately proved in OneGapLift.lean.
"""
import argparse
from datetime import datetime
import itertools
import json
from pathlib import Path
import platform
import re
import time
from zoneinfo import ZoneInfo

from check_certificate import check_document
from hansen_lift import find_underlining
from exclusion_certificate import generate
from check_exclusion import check_exclusion


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_member(a, b):
    A, B = 1 << a, 1 << b
    D, n = A + B + 1, 3 * A + B + 1
    source = [1 << i for i in range(a + 1)] + [A + 1, D, 2 * A, n]
    parents = [(i - 1, i - 1) for i in range(1, a + 1)]
    parents += [(a, 0), (a + 1, b), (a, a), (a + 3, a + 2)]
    all_parents = []
    for i, value in enumerate(source[1:], 1):
        choices = [(j, k) for j in range(i) for k in range(j + 1)
                   if source[j] + source[k] == value]
        require(parents[i - 1] in choices, 'invalid source pair')
        require(a == 2 or choices == [parents[i - 1]], 'unexpected alternative parents')
        all_parents.append(choices)

    # Every endpoint-fixed Boolean marking, with existential source summands.
    accepted = []
    masks = 0
    for bits in itertools.product((False, True), repeat=len(source) - 2):
        masks += 1
        anchor = 1
        stored = {1}
        for value, mark in zip(source[1:], bits + (True,)):
            if value - anchor not in stored:
                break
            stored.add(value)
            if mark:
                anchor = value
        else:
            accepted.append([0] + [i for i, flag in enumerate(bits, 1) if flag]
                            + [len(source) - 1])
    underlining = find_underlining(source)
    require(bool(accepted) == (underlining is not None), 'marking algorithms disagree')
    require(bool(accepted) == (a == 2 and b == 1), 'classification hypothesis failed')

    # Direct construction mirrors the order proved in Lean, using stored values.
    values, pairs, indices = [1], [], {1: 0}

    def add(left, right):
        require(left in indices and right in indices, 'missing direct summand')
        value = left + right
        require(value > values[-1], 'direct order is not strict')
        pairs.append([indices[left], indices[right]])
        indices[value] = len(values)
        values.append(value)
        return value

    for i in range(a):
        m = (1 << (1 << i)) - 1
        current = m
        for _ in range(1 << i):
            current = add(current, current)
        add(current, m)
    mA = (1 << A) - 1
    current = mA
    for _ in range(B + 1):
        current = add(current, current)
    exceptional = add(current, 1)
    repaired = add(exceptional, 2 * ((1 << B) - 1))
    require(repaired == (1 << D) - 1, 'repair identity failed')
    for _ in range(A - B - 1):
        current = add(current, current)
    current = add(current, mA)
    for _ in range(D):
        current = add(current, current)
    add(current, repaired)

    # Independent allocation: a base and all shifts through its outgoing cap.
    bases = [(1 << v) - 1 for v in source]
    bases[a + 1] = ((1 << A) - 1) * (1 << (B + 1)) + 1
    labels = [(1 << (i - 1), 0) for i in range(1, a + 1)]
    labels += [(B + 1, 0), (0, 1), (A, 0), (D, 0)]
    caps = [0] * len(source)
    for i, ((left, right), (s, t)) in enumerate(zip(parents, labels), 1):
        u, v = bases[left] << s, bases[right] << t
        require(u + v == bases[i] and (u & v) == 0, 'base sum or carry failed')
        require(bin(bases[i]).count('1') == source[i], 'wrong base bit count')
        caps[left] = max(caps[left], s)
        caps[right] = max(caps[right], t)
    require(sum(caps) == n - 1, 'doubling budget differs')
    nodes = {1: None}
    for i, base in enumerate(bases):
        for k in range(caps[i] + 1):
            if i == k == 0:
                continue
            value = base << k
            require(value not in nodes, 'allocation collision')
            if k:
                nodes[value] = (value // 2, value // 2)
            else:
                left, right = parents[i - 1]
                s, t = labels[i - 1]
                nodes[value] = (bases[left] << s, bases[right] << t)
    ordered = sorted(nodes)
    require(ordered == values, 'allocation and direct replay differ')
    require([(values[l], values[r]) for l, r in pairs] == [nodes[v] for v in ordered[1:]],
            'allocation summands and direct replay differ')
    steps = n - 1 + a + 4
    certificate = {'format': 'addition-chain-indices-v1', 'start': 1,
                   'target': {'kind': 'mersenne', 'exponent': n},
                   'additions': steps, 'pairs': pairs}
    require(check_document(certificate, exponent=n, additions=steps) == values,
            'independent certificate replay differs')
    return {'a': a, 'b': b, 'n': n, 'source': source, 'source_additions': a + 4,
            'source_parent_choices': all_parents, 'marking_masks': masks,
            'accepted_markings': accepted, 'caps': caps, 'doublings': sum(caps),
            'lift_additions': steps, 'allocated_nodes': len(nodes),
            'direct_order_equals_sorted_allocation': True,
            'independent_replay_verified': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started = time.perf_counter()
    now = datetime.now(ZoneInfo('Australia/Sydney'))
    members = [check_member(a, b) for a in range(2, 10) for b in range(1, a)]
    exclusion = generate(29, 6, node_budget=1000)
    require(exclusion['status'] == 'excluded', '29 exclusion incomplete')
    certificate = exclusion['certificate']
    independent = check_exclusion(certificate, target=29, max_steps=6)
    lean = (Path(__file__).resolve().parents[1] /
            'lean/ScholzBrauer/OneGapLift.lean').read_text()
    literal = lean.split('def exclusion29 : Array ExclusionNode :=', 1)[1].split('theorem', 1)[0]
    nodes = []
    for rule, edges in re.findall(r'\.(gap|bound|split)(?:\s*\[([^\]]*)\])?', literal):
        nodes.append([rule, [list(map(int, pair)) for pair in
                            re.findall(r'\((\d+), (\d+)\)', edges)]]
                     if rule == 'split' else [rule])
    require(nodes == certificate['nodes'] and certificate['root'] == 21,
            'Lean exclusion data differs from checked generator')
    report = {'started_at_australia_sydney': now.isoformat(),
              'python': platform.python_version(), 'seed': None,
              'domain': 'All integer pairs 2 <= a <= 9 and 1 <= b < a',
              'members': members, 'member_count': len(members),
              'exclusion29': exclusion, 'independent_exclusion29': independent,
              'marking_masks': sum(m['marking_masks'] for m in members),
              'claim_boundary': 'Exhaustive source markings in this bounded parameter range; '
                                'direct witnesses, not source or Mersenne optimality. '
                                'Infinite-family replay/count/classification separately proved in Lean.',
              'runtime_seconds': round(time.perf_counter() - started, 6)}
    if args.output:
        with args.output.open('x') as handle:
            json.dump(report, handle, indent=2)
            handle.write('\n')
    print(json.dumps({key: report[key] for key in
                      ('member_count', 'marking_masks', 'runtime_seconds')}))


if __name__ == '__main__':
    main()
