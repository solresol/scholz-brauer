#!/usr/bin/env python3
"""Independently check the saved budget certificates for Clift's 109 graph.

Reads the report of `experiment_clift109_box.py` and, without importing it:

* checks that every stored configuration partitions [0,108] exactly;
* rebuilds each case's particular labelling and its 109 explicit path weights;
* recomputes the unique weight-108 path, then re-derives every constraint of
  every stored negative cycle from its description. Each constraint must be a
  valid consequence of cost 108 (a nonnegative shift, a zero shift at a tail
  off the path, or a path edge dominating a sibling), and the cycle must
  telescope to 0 <= negative. Hence no case admits a cost-108 gauge;
* checks each stored optimal labelling is a nonnegative gauge of its case
  with the stored cost >= 109, and replays one 120-addition allocation.

It does not re-run the enumeration; completeness is the experiment's claim.
Standard library only; exact integers.
"""
import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path

from experiment_clift109 import SOURCE, PARENTS, check_allocation

N = 109
PARENT = {SOURCE[i]: (SOURCE[p], SOURCE[q]) for i, (p, q) in enumerate(PARENTS, 1)}
NAMES = ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta', 'theta',
         'iota', 'kappa', 'lambda', 'mu', 'nu', 'xi', 'pi', 'rho', 'sigma', 'tau',
         'phi', 'chi', 'psi', 'omega']
EDGE = {name: (SOURCE[1 + i // 2], i % 2) for i, name in enumerate(NAMES)}


def fail(message):
    raise ValueError(message)


def partition(cfg):
    u, v, w, d1, d2, d3, t, p, q, A1, A2, A3 = cfg
    values = [t + sum(c) for r in range(7) for c in combinations((u, v, w, d1, d2, d3), r)]
    R7 = [0, d1, d2, d1 + d2, p]
    R5 = R7 + [q, q + d1]
    values += [A1 + x + y for x in (0, u, v, u + v) for y in R5]
    values += [A2 + x + y for x in (0, u) for y in R7]
    values += [A3 + y for y in R5]
    return sorted(values) == list(range(N))


def labelling(cfg, swap, orient):
    u, v, w, d1, d2, d3, t, p, q, A1, A2, A3 = cfg
    if swap:
        w, d3 = d3, w
    o1, o2, o3 = orient
    shifts = {'alpha': u, 'beta': 0, 'gamma': v, 'delta': 0, 'iota': w + t, 'kappa': t,
              'epsilon': A1, 'zeta': A3, 'eta': 0, 'theta': A2, 'mu': 0, 'nu': 0,
              'lambda': 0 if o3 else d3, 'xi': d3 if o3 else 0, 'sigma': 0, 'rho': q,
              'pi': 0 if o2 else d2, 'tau': d2 if o2 else 0, 'psi': 0, 'chi': p,
              'phi': 0 if o1 else d1, 'omega': d1 if o1 else 0}
    return shifts


def paths(vertex=109):
    if vertex == 1:
        return [[]]
    out = []
    for k in (0, 1):
        name = NAMES[2 * (SOURCE.index(vertex) - 1) + k]
        out += [path + [name] for path in paths(PARENT[vertex][k])]
    return out


PATHS = paths()


def weights(shifts):
    return sorted(sum(shifts[e] for e in path) for path in PATHS)


def tail(name):
    vertex, k = EDGE[name]
    return PARENT[vertex][k]


def head(name):
    return EDGE[name][0]


def node(vertex):
    return 'Z' if vertex in (1, 109) else vertex


def heaviest_path(shifts):
    found = [path for path in PATHS if sum(shifts[e] for e in path) == N - 1]
    if len(found) != 1:
        fail('weight 108 is not attained by exactly one path')
    return found[0]


def check_cycle(shifts, cycle, path):
    on_path = set(path)
    path_tails = {tail(e) for e in path}
    balance = Counter()
    total = 0
    for a, b, c, kind, *names in cycle:
        if kind == 'nonnegative':
            (e,) = names
            expected = (node(tail(e)), node(head(e)), shifts[e])
        elif kind == 'zero off path':
            (e,) = names
            if tail(e) in path_tails:
                fail('zero constraint at a tail on the path')
            expected = (node(head(e)), node(tail(e)), -shifts[e])
        elif kind == 'path edge dominates':
            ep, e = names
            if ep not in on_path or e in on_path or tail(ep) != tail(e):
                fail('invalid domination constraint')
            expected = (node(head(e)), node(head(ep)), shifts[ep] - shifts[e])
        else:
            fail(f'unknown constraint {kind}')
        a = 'Z' if a == 'Z' else int(a)
        b = 'Z' if b == 'Z' else int(b)
        if (a, b, c) != expected:
            fail('stored constraint differs from its description')
        balance[a] += 1
        balance[b] -= 1
        total += c
    if any(balance.values()) or total >= 0:
        fail('certificate does not telescope to a contradiction')
    return total


def check_report(report):
    configs = [tuple(c) for c in report['configurations']]
    if len(set(configs)) != len(configs) or not all(partition(c) for c in configs):
        fail('stored configurations do not partition [0,108]')
    cases = report['case_records']
    expected = {(c, s, o) for c in configs for s in (0, 1) for o in product((0, 1), repeat=3)}
    seen = {(tuple(r['configuration']), r['swap_w_d3'], tuple(r['orientation'])) for r in cases}
    if seen != expected or len(cases) != len(expected):
        fail('cases do not cover every configuration, role and orientation')
    minima = Counter()
    witness = None
    for record in cases:
        shifts = labelling(tuple(record['configuration']), record['swap_w_d3'],
                           tuple(record['orientation']))
        if weights(shifts) != list(range(N)):
            fail('particular labelling is not an interval labelling')
        path = heaviest_path(shifts)
        check_cycle(shifts, record['negative_cycle'], path)
        optimal = {}
        for i, vertex in enumerate(SOURCE[1:]):
            for k in (0, 1):
                optimal[NAMES[2 * i + k]] = record['optimal_shifts'][i][k]
        if min(optimal.values()) < 0 or weights(optimal) != list(range(N)):
            fail('stored optimum is not a valid labelling')
        # same gauge class: differences along every edge come from potentials
        g = {1: 0}
        for vertex in SOURCE[1:]:
            name = NAMES[2 * (SOURCE.index(vertex) - 1)]
            g[vertex] = optimal[name] - shifts[name] + g[PARENT[vertex][0]]
        if g[109] != 0 or any(optimal[e] - shifts[e] != g[head(e)] - g[tail(e)] for e in NAMES):
            fail('stored optimum is not a gauge of its case')
        caps = Counter()
        for e in NAMES:
            caps[tail(e)] = max(caps[tail(e)], optimal[e])
        cost = sum(caps.values())
        if cost != record['minimum_cost'] or cost < 109:
            fail('stored minimum cost differs')
        minima[cost] += 1
        if cost == 109 and witness is None:
            witness = optimal
    if dict(sorted(minima.items())) != {int(k): v for k, v in
                                        report['minimum_cost_histogram'].items()}:
        fail('minimum histogram differs')
    # replay one minimum through the existing independent chain checker
    sets = {1: [0]}
    for i, vertex in enumerate(SOURCE[1:]):
        p, q = PARENT[vertex]
        a, b = witness[NAMES[2 * i]], witness[NAMES[2 * i + 1]]
        sets[vertex] = [x + a for x in sets[p]] + [x + b for x in sets[q]]
    bases = [sum(1 << x for x in sets[v]) for v in SOURCE]
    labels = [(witness[NAMES[2 * i]], witness[NAMES[2 * i + 1]]) for i in range(11)]
    document = check_allocation(bases, labels)
    if document['additions'] != 120:
        fail('witness allocation length')
    return {'configurations': len(configs), 'cases': len(cases),
            'negative_cycles_checked': len(cases), 'minimum_doublings': min(minima),
            'minimum_cost_histogram': dict(sorted(minima.items())),
            'replayed_additions': document['additions']}


def corruption_tests(report):
    """Each corrupted copy of the saved report must be rejected."""
    def constant(r):
        r['case_records'][5]['negative_cycle'][0][2] -= 1

    def dropped(r):
        r['case_records'][7]['negative_cycle'].pop()

    def kind(r):
        for c in r['case_records'][9]['negative_cycle']:
            if c[3] == 'nonnegative':
                c[3] = 'zero off path'
                break

    def missing(r):
        r['case_records'].pop(100)

    def configuration(r):
        r['configurations'][3][7] += 1

    def minimum(r):
        r['case_records'][0]['minimum_cost'] -= 1

    def optimum(r):
        r['case_records'][1]['optimal_shifts'][0][0] += 1

    rejected = 0
    for mutate in (constant, dropped, kind, missing, configuration, minimum, optimum):
        corrupted = json.loads(json.dumps(report))
        mutate(corrupted)
        try:
            check_report(corrupted)
        except ValueError:
            rejected += 1
        else:
            fail(f'corruption {mutate.__name__} was accepted')
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('report', type=Path)
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    summary = check_report(report)
    summary['rejected_corruptions'] = corruption_tests(report)
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
