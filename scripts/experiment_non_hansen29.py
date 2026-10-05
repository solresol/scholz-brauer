#!/usr/bin/env python3
"""Exact fixed-spine labelling experiment on Clift's non-Hansen 29 graph.

No random choices, third-party dependencies, or general labelling claims.
All unfixed labels are nonnegative and bounded by the 28-doubling budget.
The existing certificate checker independently verifies the resulting chain.
"""
import argparse
from datetime import datetime
import itertools
import json
from pathlib import Path
import platform
import time
from zoneinfo import ZoneInfo

from check_certificate import check_document
from hansen_lift import find_underlining

ROOT = Path(__file__).resolve().parents[1]
SOURCE = [1, 2, 4, 8, 9, 13, 16, 29]
PARENTS = [(0, 0), (1, 1), (2, 2), (3, 0), (4, 2), (3, 3), (6, 5)]
TARGET = (1 << 29) - 1


def require(condition, message):
    if not condition:
        raise ValueError(message)


def experiment():
    # Check *all* possible unordered decompositions, not just chosen parents.
    for i, value in enumerate(SOURCE[1:], 1):
        pairs = [(j, k) for j in range(i) for k in range(j + 1)
                 if SOURCE[j] + SOURCE[k] == value]
        require(pairs == [PARENTS[i - 1]], 'source parent is not unique')
    accepted_masks = []
    for bits in itertools.product((False, True), repeat=6):
        marks = (True,) + bits + (True,)
        anchor = 0
        valid = True
        for i in range(1, 8):
            if SOURCE[i] - SOURCE[anchor] not in SOURCE[:i]:
                valid = False
                break
            if marks[i]:
                anchor = i
        if valid:
            accepted_masks.append(marks)
    require(not accepted_masks and find_underlining(SOURCE) is None,
            'source unexpectedly Hansen')

    # Standard local M_(x+y) = 2^y M_x + M_y: exhaust every orientation.
    orientations = []
    for bits in itertools.product((0, 1), repeat=3):
        caps = [0] * 8
        choice = iter(bits)
        for left, right in PARENTS:
            if left != right and next(choice):
                left, right = right, left
            caps[left] = max(caps[left], SOURCE[right])
        orientations.append({'choices': bits, 'caps': caps, 'doublings': sum(caps)})
    require(min(row['doublings'] for row in orientations) == 32,
            'unexpected Mersenne orientation minimum')

    # Hold bases at 1,2,4,8,16 equal to M_v; leave 9 and 13 arbitrary.
    # B9 = 2^a*255 + 2^b, B13 = 2^c*B9 + 2^d*15,
    # T = 2^e*65535 + 2^f*B13.
    # Caps are [max(1,b),2,max(4,d),max(8,a),c,f,e,0].
    # All labels are <=28. Positive terms >T cannot occur in a solution.
    # Recover f exactly from the final quotient, covering all f without a loop.
    solutions = []
    terminal_checks = 0
    for a in range(29):
        for b in range(29):
            base9 = (255 << a) + (1 << b)
            partial = max(1, b) + 2 + 4 + max(8, a)
            if base9 > TARGET or partial > 28:
                continue
            for c in range(29 - partial):
                for d in range(29):
                    base13 = (base9 << c) + (15 << d)
                    subtotal = max(1, b) + 2 + max(4, d) + max(8, a) + c
                    if base13 > TARGET or subtotal > 28:
                        continue
                    for e in range(29 - subtotal):
                        terminal_checks += 1
                        remainder = TARGET - (65535 << e)
                        if remainder <= 0 or remainder % base13:
                            continue
                        quotient = remainder // base13
                        if quotient & (quotient - 1):
                            continue
                        f = quotient.bit_length() - 1
                        if subtotal + e + f <= 28:
                            solutions.append({'labels': [a, b, c, d, e, f],
                                              'base9': base9, 'base13': base13,
                                              'doublings': subtotal + e + f})
    require(solutions == [{'labels': [5, 0, 0, 1, 13, 0], 'base9': 8161,
                           'base13': 8191, 'doublings': 28}],
            'restricted solution set changed')

    # Reverse enumeration checks the same finite solution set via exact division.
    # Unlike the forward search it loops every c,d,e,f in 0..28 and derives b.
    reverse = []
    for e, f in itertools.product(range(29), repeat=2):
        rest = TARGET - (65535 << e)
        if rest <= 0 or rest % (1 << f):
            continue
        base13 = rest >> f
        for c, d in itertools.product(range(29), repeat=2):
            rest9 = base13 - (15 << d)
            if rest9 <= 0 or rest9 % (1 << c):
                continue
            base9 = rest9 >> c
            for a in range(29):
                power = base9 - (255 << a)
                if power <= 0 or power & (power - 1):
                    continue
                b = power.bit_length() - 1
                cost = max(1, b) + 2 + max(4, d) + max(8, a) + c + e + f
                if b <= 28 and cost <= 28:
                    reverse.append([a, b, c, d, e, f])
    require(reverse == [row['labels'] for row in solutions],
            'forward and reverse exhaustive enumerations differ')

    bases = [1, 3, 15, 255, 8161, 8191, 65535, TARGET]
    labels = [(1, 0), (2, 0), (4, 0), (5, 0), (0, 1), (8, 0), (13, 0)]
    caps = [0] * 8
    for i, ((left, right), (a, b)) in enumerate(zip(PARENTS, labels), 1):
        require((bases[left] << a) + (bases[right] << b) == bases[i],
                'incorrect base sum')
        require(bin(bases[i]).count('1') == SOURCE[i], 'incorrect bit count')
        require(not ((bases[left] << a) & (bases[right] << b)), 'bit carry')
        caps[left] = max(caps[left], a)
        caps[right] = max(caps[right], b)
    require(sum(caps) == 28, 'incorrect doubling budget')
    nodes = {1: None}
    for i, base in enumerate(bases):
        for k in range(caps[i] + 1):
            value = base << k
            if i == k == 0:
                continue
            require(value not in nodes, 'duplicate allocated value')
            if k:
                pair = [value // 2, value // 2]
            else:
                left, right = PARENTS[i - 1]
                a, b = labels[i - 1]
                pair = [bases[left] << a, bases[right] << b]
            nodes[value] = pair
    values = sorted(nodes)
    indices = {v: i for i, v in enumerate(values)}
    certificate = {'format': 'addition-chain-indices-v1', 'start': 1,
                   'target': {'kind': 'mersenne', 'exponent': 29}, 'additions': 35,
                   'source_chain': SOURCE,
                   'pairs': [[indices[a], indices[b]] for a, b in
                             (nodes[v] for v in values[1:])]}
    require(check_document(certificate, exponent=29, additions=35) == values,
            'independent replay differs')
    provenance = json.loads((ROOT / 'data/2026-10-06-non-hansen29-source.json').read_text())
    require(provenance['chain'] == SOURCE, 'published source differs')
    published_prefix = provenance['displayed_lift_prefix']
    require(values[:len(published_prefix)] == published_prefix,
            'published prefix differs')
    require(values[-2:] == provenance['displayed_lift_final_two'],
            'published endpoint differs')
    return {'source': SOURCE, 'unique_parents': PARENTS,
            'marking_masks': 64, 'accepted_markings': accepted_masks,
            'mersenne_orientations': orientations,
            'fixed_spine': [1, 2, 4, 8, 16], 'label_range': [0, 28],
            'doubling_budget': 28, 'terminal_checks': terminal_checks,
            'solutions': solutions, 'reverse_solutions': reverse, 'bases': bases, 'labels': labels, 'caps': caps,
            'values': values, 'certificate': certificate,
            'claim_boundary': 'Exhaustive only for the specified fixed-spine graph; '
                              'no optimality or general extension theorem.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.perf_counter()
    run_time = datetime.now(ZoneInfo('Australia/Sydney')).isoformat()
    report = experiment()
    # Compare the checked certificate with the separately stored Lean literals.
    import re
    lean = (ROOT / 'lean/ScholzBrauer/NonHansen29.lean').read_text()
    literal = lean.split('def liftedSteps : List Step :=', 1)[1].split('\n\ndef', 1)[0]
    pairs = [tuple(map(int, p)) for p in re.findall(r'\((\d+), (\d+)\)', literal)]
    expected = [(report['values'][a], report['values'][b])
                for a, b in report['certificate']['pairs']]
    require(pairs == expected, 'Lean literal pairs differ from the checked allocation')
    report.update({'started_at_australia_sydney': run_time,
                   'python': platform.python_version(), 'seed': None,
                   'runtime_seconds': round(time.perf_counter() - start, 6)})
    if args.output:
        with args.output.open('x') as handle:
            json.dump(report, handle, indent=2)
            handle.write('\n')
    print(json.dumps({'solutions': report['solutions'],
                      'terminal_checks': report['terminal_checks'],
                      'runtime_seconds': report['runtime_seconds']}))


if __name__ == '__main__':
    main()
