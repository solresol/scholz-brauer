#!/usr/bin/env python3
"""Complete budget analysis of Clift's selected 109 graph via the 8-box.

A labelling assigns a nonnegative shift to each of the 22 edges; B1=1 and
B_v=2^a B_p+2^b B_q. Then B109 is the sum of 2^weight over all 109 source-sink
paths, so B109=M109 forces 109 distinct weights (binary weight). A cap sum at
most 108 bounds every path weight by 108, hence the weights are exactly
{0,...,108}: an *interval labelling*. Conversely every labelling costs at
least its largest path weight, 108.

The 64 paths through vertex 8 have weights t+SS(u,v,w,d1,d2,d3), forcing six
positive differences with distinct subset sums. Two independent programs
enumerate every interval configuration from this box. Every labelling of an
enumerated configuration is a fixed particular labelling plus a gauge (add g_v
to the two in-shifts of v and subtract it from its out-shifts). For each
configuration, role and orientation we then:

* prove budget 108 infeasible by a negative cycle of difference constraints
  forced by the unique weight-108 path, and
* compute the exact minimum cap sum by a min-cost flow, with an explicit
  primal labelling and equal dual value.

Finally the enumeration is compared with every earlier restricted family.
Exact integers and the standard library only; random self-tests use a recorded
seed. This is a computational proof, not a Lean theorem.
"""
import argparse
from collections import Counter, defaultdict
from datetime import datetime
import hashlib
import itertools
import json
from pathlib import Path
import platform
import random
import subprocess
import sys
import tempfile
import time
from zoneinfo import ZoneInfo

from experiment_clift109 import ROOT, SOURCE, PARENTS, require, mersenne, check_allocation
import clift109_box_dual

N = 109
VERTS = SOURCE
PAR = {SOURCE[i]: (SOURCE[p], SOURCE[q]) for i, (p, q) in enumerate(PARENTS, 1)}
EDGES = [(v, k) for v in VERTS[1:] for k in (0, 1)]
INTER = VERTS[1:-1]
TAILS = VERTS[:-1]
CHILDREN = defaultdict(list)
for _v, _k in EDGES:
    CHILDREN[PAR[_v][_k]].append((_v, _k))
GREEK = {(2, 0): 'alpha', (2, 1): 'beta', (4, 0): 'gamma', (4, 1): 'delta',
         (5, 0): 'epsilon', (5, 1): 'zeta', (7, 0): 'eta', (7, 1): 'theta',
         (8, 0): 'iota', (8, 1): 'kappa', (15, 0): 'lambda', (15, 1): 'mu',
         (23, 0): 'nu', (23, 1): 'xi', (28, 0): 'pi', (28, 1): 'rho',
         (51, 0): 'sigma', (51, 1): 'tau', (58, 0): 'phi', (58, 1): 'chi',
         (109, 0): 'psi', (109, 1): 'omega'}


# ---------------------------------------------------------------- model ----

def all_paths(v=109):
    if v == 1:
        return [[]]
    return [p + [(v, k)] for k in (0, 1) for p in all_paths(PAR[v][k])]


PATHS = all_paths()
require(len(PATHS) == 109, 'path count')


def path_weights(L):
    """Weights of the 109 explicit paths (no set recursion)."""
    return sorted(sum(L[v][k] for v, k in p) for p in PATHS)


def weight_sets(L):
    S = {1: [0]}
    for v in VERTS[1:]:
        S[v] = sorted([x + L[v][0] for x in S[PAR[v][0]]] +
                      [x + L[v][1] for x in S[PAR[v][1]]])
    return S


def caps_of(L):
    caps = {u: 0 for u in TAILS}
    for v, k in EDGES:
        caps[PAR[v][k]] = max(caps[PAR[v][k]], L[v][k])
    return caps


def cost_of(L):
    return sum(caps_of(L).values())


def box_six(cfg):
    return cfg[:6]


def decomposition(cfg):
    u, v, w, d1, d2, d3, t, p, q, A1, A2, A3 = cfg
    six = (u, v, w, d1, d2, d3)
    box = [t + sum(c) for r in range(7) for c in itertools.combinations(six, r)]
    R7 = [0, d1, d2, d1 + d2, p]
    R5 = R7 + [q, q + d1]
    b1 = [A1 + x + y for x in (0, u, v, u + v) for y in R5]
    b2 = [A2 + x + y for x in (0, u) for y in R7]
    b3 = [A3 + y for y in R5]
    return sorted(box + b1 + b2 + b3)


def invariants(L):
    """Gauge invariants and orientation bits of an arbitrary labelling."""
    g = {GREEK[e]: L[e[0]][e[1]] for e in EDGES}
    flip = {'u': g['alpha'] < g['beta'], 'v': g['gamma'] < g['delta'],
            'w': g['iota'] < g['kappa']}
    lam, mu = g['lambda'] + g['nu'], g['mu'] + g['nu']
    pi_, rho = g['pi'] + g['sigma'], g['rho'] + g['sigma']
    phi, chi = g['phi'] + g['psi'], g['chi'] + g['psi']
    u = abs(g['alpha'] - g['beta']); v = abs(g['gamma'] - g['delta'])
    w = abs(g['iota'] - g['kappa'])
    d3 = abs(lam - g['xi']); d2 = abs(pi_ - g['tau']); d1 = abs(phi - g['omega'])
    orient = (0 if phi >= g['omega'] else 1, 0 if pi_ >= g['tau'] else 1,
              0 if lam >= g['xi'] else 1)
    m2 = min(g['alpha'], g['beta']); m4 = m2 + min(g['gamma'], g['delta'])
    m8 = m4 + min(g['iota'], g['kappa'])
    r51 = min(phi, g['omega']); r23 = min(pi_, g['tau']) + r51
    r8 = min(lam, g['xi']) + r23
    base7 = mu + r23
    cfg = (u, v, w, d1, d2, d3, m8 + r8, chi - base7,
           rho + r51 - g['eta'] - base7, m4 + g['epsilon'] + g['eta'] + base7,
           m2 + g['theta'] + base7, g['zeta'] + g['eta'] + base7)
    return cfg, orient, flip


def particular(cfg, swap_wd3, orient):
    """One labelling with the given invariants (shifts may be negative)."""
    u, v, w, d1, d2, d3, t, p, q, A1, A2, A3 = cfg
    if swap_wd3:
        w, d3 = d3, w
    o1, o2, o3 = orient
    return {2: (u, 0), 4: (v, 0), 8: (w + t, t), 5: (A1, A3), 7: (0, A2),
            15: (0 if o3 else d3, 0), 23: (0, d3 if o3 else 0),
            28: (0 if o2 else d2, q), 51: (0, d2 if o2 else 0),
            58: (0 if o1 else d1, p), 109: (0, d1 if o1 else 0)}


def gauge(L, g):
    g = dict(g); g[1] = 0; g[109] = 0
    return {v: tuple(L[v][k] + g[v] - g[PAR[v][k]] for k in (0, 1)) for v in VERTS[1:]}


def gauge_difference(L, M):
    """Return g with M = gauge(L, g), or None. Solved along in-edges then checked."""
    g = {1: 0}
    for v in VERTS[1:]:
        p = PAR[v][0]
        g[v] = M[v][0] - L[v][0] + g[p]
    if g[109] != 0:
        return None
    for v, k in EDGES:
        if M[v][k] != L[v][k] + g[v] - g[PAR[v][k]]:
            return None
    return {v: g[v] for v in INTER}


def canonical_parallel(L):
    """Put the larger shift first on each parallel equal-parent pair."""
    M = dict(L)
    for v in (2, 4, 8):
        M[v] = tuple(sorted(L[v], reverse=True))
    return M


# ------------------------------------------------------ difference systems --

def node(v):
    return 'Z' if v in (1, 109) else v


def label_constraints(L):
    """Every shift is nonnegative: g_tail - g_head <= s0."""
    return [(node(PAR[v][k]), node(v), L[v][k], ('nonnegative', GREEK[(v, k)]))
            for v, k in EDGES]


def bellman_ford(cons, nodes):
    """Feasible potentials, or a negative cycle as a list of constraints."""
    dist = {n: 0 for n in nodes}
    pred = {n: None for n in nodes}
    last = None
    for _ in range(len(nodes) + 1):
        last = None
        for i, (a, b, c, _) in enumerate(cons):
            if dist[b] + c < dist[a]:
                dist[a] = dist[b] + c
                pred[a] = i
                last = a
        if last is None:
            return dist, None
    x = last
    for _ in range(len(nodes)):
        x = cons[pred[x]][1]
    cycle, y = [], x
    while True:
        i = pred[y]
        cycle.append(i)
        y = cons[i][1]
        if y == x:
            break
    return None, [cons[i] for i in reversed(cycle)]


def check_negative_cycle(cycle):
    """Independent check: the constraints telescope to 0 <= negative."""
    balance = Counter()
    for a, b, c, _ in cycle:
        balance[a] += 1
        balance[b] -= 1
    require(all(x == 0 for x in balance.values()), 'certificate is not a cycle')
    total = sum(c for _, _, c, _ in cycle)
    require(total < 0, 'certificate is not negative')
    return total


def critical_path(L):
    S = weight_sets(L)
    require(S[109] == list(range(N)), 'not an interval labelling')
    path, v, target = [], 109, N - 1
    while v != 1:
        hits = [k for k in (0, 1) if max(S[PAR[v][k]]) + L[v][k] == target]
        require(len(hits) == 1, 'maximum is not unique')
        k = hits[0]
        path.append((v, k))
        target -= L[v][k]
        v = PAR[v][k]
    require(target == 0, 'critical path weight')
    return list(reversed(path))


def budget108(L):
    """Constraints forced by cost 108; returns (labels, None) or (None, cycle)."""
    path = critical_path(L)
    on = set(path)
    tails = {PAR[v][k] for v, k in path}
    cons = label_constraints(L)
    for v, k in EDGES:
        t = PAR[v][k]
        if t not in tails:
            cons.append((node(v), node(t), -L[v][k], ('zero off path', GREEK[(v, k)])))
    for t in TAILS:
        if t in tails:
            (vp, kp), = [e for e in CHILDREN[t] if e in on]
            for v, k in CHILDREN[t]:
                if (v, k) != (vp, kp):
                    cons.append((node(v), node(vp), L[vp][kp] - L[v][k],
                                 ('path edge dominates', GREEK[(vp, kp)], GREEK[(v, k)])))
    dist, cycle = bellman_ford(cons, ['Z'] + INTER)
    if cycle is not None:
        return None, cycle, path
    g = {v: dist[v] - dist['Z'] for v in INTER}
    return gauge(L, g), None, path


def min_cost(L, fixed=None):
    """Exact minimum cap sum over all nonnegative gauges with g fixed on `fixed`.

    Primal: minimise sum_u (top_u - g_u) subject to g_tail - g_head <= s0 and
    g_head - top_tail <= -s0. The dual is a min-cost flow with unit supplies at
    the free g nodes and Z and unit demands at the top nodes; fixed g nodes are
    merged into Z with adjusted arc costs. Successive shortest paths give the
    flow; residual potentials give a primal labelling with the same value.
    """
    fixed = dict(fixed or {})
    fixed_val = {'Z': 0}
    for v, val in fixed.items():
        fixed_val[v] = val
    free = [v for v in INTER if v not in fixed]

    def gn(v):
        n = node(v)
        return 'Z' if n in fixed_val else n

    def off(v):
        return fixed_val.get(node(v), 0)

    nodes = ['S', 'T', 'Z'] + free + [('P', u) for u in TAILS]
    idx = {n: i for i, n in enumerate(nodes)}
    graph = [[] for _ in nodes]

    def arc(a, b, cap, cost):
        ia, ib = idx[a], idx[b]
        graph[ia].append([ib, cap, cost, len(graph[ib])])
        graph[ib].append([ia, 0, -cost, len(graph[ia]) - 1])

    big = 10 ** 9
    shifted = [(gn(PAR[v][k]), gn(v), L[v][k] + off(v) - off(PAR[v][k]), None)
               for v, k in EDGES]
    if bellman_ford(shifted, ['Z'] + free)[1] is not None:
        return None  # the fixed gauges force a negative shift
    for v, k in EDGES:
        t, s0 = PAR[v][k], L[v][k]
        # x_t - x_v <= s0 with fixed parts moved into the constant
        arc(gn(t), gn(v), big, s0 + off(v) - off(t))
        # x_v - P_t <= -s0
        arc(gn(v), ('P', t), big, -s0 - off(v))
    arc('S', 'Z', 1 + len(fixed), 0)
    for v in free:
        arc('S', v, 1, 0)
    for u in TAILS:
        arc(('P', u), 'T', 1, 0)
    # objective constant from fixed g_u (coefficient -1 for every tail u != 1)
    constant = -sum(fixed_val[node(u)] for u in TAILS if node(u) in fixed_val and u != 1)
    S, T = idx['S'], idx['T']
    total = 0
    for _ in TAILS:
        dist = [None] * len(nodes); dist[S] = 0; prev = [None] * len(nodes)
        for _ in range(len(nodes)):
            changed = False
            for a in range(len(nodes)):
                if dist[a] is None:
                    continue
                for j, (b, cap, cost, _) in enumerate(graph[a]):
                    if cap > 0 and (dist[b] is None or dist[a] + cost < dist[b]):
                        dist[b] = dist[a] + cost; prev[b] = (a, j); changed = True
            if not changed:
                break
        else:
            raise ValueError('negative residual cycle')
        if dist[T] is None:
            return None
        b = T
        while b != S:
            a, j = prev[b]
            graph[a][j][1] -= 1
            graph[graph[a][j][0]][graph[a][j][3]][1] += 1
            b = a
        total += dist[T]
    d = [0] * len(nodes)
    for _ in range(len(nodes) + 1):
        changed = False
        for a in range(len(nodes)):
            for b, cap, cost, _ in graph[a]:
                if cap > 0 and d[a] + cost < d[b]:
                    d[b] = d[a] + cost; changed = True
        if not changed:
            break
    else:
        raise ValueError('negative residual cycle at optimum')
    g = {v: d[idx['Z']] - d[idx[v]] for v in free}
    g.update(fixed)
    M = gauge(L, g)
    require(all(s >= 0 for pr in M.values() for s in pr), 'negative optimal shift')
    value = constant - total
    require(cost_of(M) == value, 'primal and dual values differ')
    return value, M


def feasible_points(L, fixed):
    """All integer gauges (nonnegative shifts) with g fixed on `fixed`.

    The closure of a consistent difference system is decomposable: assigning
    variables in turn within their closed bounds never dead-ends.
    """
    nodes = ['Z'] + INTER
    D = {a: {b: (0 if a == b else None) for b in nodes} for a in nodes}

    def tighten(a, b, c):  # x_a - x_b <= c  ->  D[b][a] = bound on x_a - x_b
        if D[b][a] is None or c < D[b][a]:
            D[b][a] = c

    for a, b, c, _ in label_constraints(L):
        tighten(a, b, c)
    for v, val in fixed.items():
        tighten(v, 'Z', val); tighten('Z', v, -val)
    for k in nodes:
        for i in nodes:
            if D[i][k] is None:
                continue
            for j in nodes:
                if D[k][j] is not None and (D[i][j] is None or D[i][k] + D[k][j] < D[i][j]):
                    D[i][j] = D[i][k] + D[k][j]
    if any(D[n][n] < 0 for n in nodes):
        return
    order = [v for v in INTER if v not in fixed]
    assigned = {'Z': 0}
    assigned.update(fixed)

    def rec(i):
        if i == len(order):
            yield {v: assigned[v] for v in INTER}
            return
        j = order[i]
        lo = max(assigned[a] - D[j][a] for a in assigned)
        hi = min(assigned[a] + D[a][j] for a in assigned)
        for x in range(lo, hi + 1):
            assigned[j] = x
            yield from rec(i + 1)
        del assigned[j]

    yield from rec(0)


# ------------------------------------------------------------- self tests --

def random_model_tests(seed, count):
    """Weights and gauge structure of arbitrary (not interval) labellings."""
    rng = random.Random(seed)
    for _ in range(count):
        L = {v: (rng.randrange(40), rng.randrange(40)) for v in VERTS[1:]}
        require(path_weights(L) == weight_sets(L)[109], 'path expansion differs')
        cfg, orient, flip = invariants(L)
        require(decomposition(cfg) == path_weights(L), 'box decomposition differs')
        M = dict(L)
        for v, name in ((2, 'u'), (4, 'v'), (8, 'w')):
            if flip[name]:
                M[v] = (L[v][1], L[v][0])
        P = particular(cfg, False, orient)
        require(gauge_difference(P, M) is not None, 'labelling is not particular plus gauge')
    return count


def standard_mersenne_labels(bits):
    choices = iter(bits)
    labels = {}
    for i, (p, q) in enumerate(PARENTS, 1):
        a, b = SOURCE[p], SOURCE[q]
        labels[SOURCE[i]] = (0, a) if p != q and next(choices) else (b, 0)
    return labels


def known_witness_tests():
    """Known labellings from earlier experiments map into the enumeration."""
    out = {}
    standard = [standard_mersenne_labels(bits) for bits in itertools.product((0, 1), repeat=8)]
    out['standard'] = standard
    # 16 October fixed-B58 109-doubling witness for (k,l)=(0,0)
    out['fixed58_109'] = {2: (1, 0), 4: (2, 0), 5: (2, 1), 7: (1, 0), 8: (4, 0), 15: (7, 0),
                          23: (0, 15), 28: (6, 0), 51: (22, 0), 58: (7, 0), 109: (0, 58)}
    return out


# --------------------------------------------------------------- driver ----

def run_cpp(workdir):
    source = ROOT / 'scripts/clift109_box_search.cpp'
    binary = workdir / 'clift109_box_search'
    compiler = ['c++', '-O2', '-std=c++17', '-Wall', '-Wextra', '-Werror']
    subprocess.run(compiler + ['-o', str(binary), str(source)], check=True)
    version = subprocess.run(['c++', '--version'], capture_output=True, text=True).stdout.splitlines()[0]
    out = workdir / 'cpp_configs.txt'
    begin = time.perf_counter()
    result = subprocess.run([str(binary), str(out)], check=True, capture_output=True, text=True)
    seconds = time.perf_counter() - begin
    stats = json.loads(result.stdout)
    stats['seconds'] = round(seconds, 6)
    stats['compiler'] = version
    stats['flags'] = compiler[1:]
    configs = sorted(tuple(map(int, line.split())) for line in out.read_text().splitlines())
    return configs, stats


def analyse(configs):
    cases = []
    histogram = Counter()
    critical = Counter()
    minimal = []
    for cfg in configs:
        for swap in (0, 1):
            for orient in itertools.product((0, 1), repeat=3):
                L = particular(cfg, swap, orient)
                require(path_weights(L) == list(range(N)), 'configuration is not an interval')
                labels, cycle, path = budget108(L)
                require(labels is None, 'BUDGET 108 LABELLING FOUND')
                total = check_negative_cycle(cycle)
                value, M = min_cost(L)
                require(value >= 109, 'minimum below 109')
                require(path_weights(M) == list(range(N)), 'optimal labelling invalid')
                histogram[value] += 1
                critical[tuple(PAR[v][k] for v, k in path) + (109,)] += 1
                case = {'configuration': cfg, 'swap_w_d3': swap, 'orientation': orient,
                        'critical_path': [PAR[v][k] for v, k in path] + [109],
                        'negative_cycle_sum': total,
                        'negative_cycle': [[a, b, c] + list(d) for a, b, c, d in cycle],
                        'minimum_cost': value,
                        'optimal_shifts': [list(M[v]) for v in VERTS[1:]]}
                cases.append(case)
                if value == 109:
                    minimal.append(case)
    return cases, histogram, critical, minimal


def cross_checks(configs):
    """Recount every earlier restricted family from the complete enumeration.

    Each family fixes some bases to Mersenne values (S_v = [0, v-1]), which
    fixes g_v when S_v has interval shape. All labellings in a family are the
    nonnegative gauge points of the interval-shaped cases, one per point: the
    particular labellings are distinct and gauges preserve every difference.
    """
    particulars = []
    for cfg in configs:
        for s in (0, 1):
            for o in itertools.product((0, 1), repeat=3):
                L = particular(cfg, s, o)
                S = weight_sets(L)
                lows = {v: S[v][0] for v in VERTS}
                shapes = {v: sum(1 << (x - S[v][0]) for x in S[v]) for v in VERTS}
                particulars.append((L, lows, shapes))

    def restricted(positions):
        for L, lows, shapes in particulars:
            fixed = {}
            for v, lo in positions.items():
                if shapes[v] != (1 << v) - 1:
                    break
                fixed[v] = lo - lows[v]
            else:
                yield L, fixed, lows, shapes

    def family(positions, free):
        """Counts, cost histogram and minimising base tuples of one family."""
        bases, minimal_bases, hist = set(), set(), Counter()
        labellings = 0
        packed = set()
        for L, fixed, lows, shapes in restricted(positions):
            for g in feasible_points(L, fixed):
                g = dict(g); g[1] = 0; g[109] = 0
                caps = dict.fromkeys(TAILS, 0)
                key = 0
                for v, k in EDGES:
                    t = PAR[v][k]
                    sh = L[v][k] + g[v] - g[t]
                    if sh > caps[t]:
                        caps[t] = sh
                    key = (key << 7) | sh
                labellings += 1
                packed.add(key)
                cost = sum(caps.values())
                hist[cost] += 1
                b = tuple(shapes[v] << (lows[v] + g[v]) for v in free)
                bases.add(b)
                if cost == 110:
                    minimal_bases.add(b)
        require(len(packed) == labellings, 'a labelling was produced twice')
        return {'base_assignments': len(bases), 'labellings': labellings,
                'minimum': min(hist), 'histogram': {str(k): n for k, n in sorted(hist.items())},
                'bases_at_110': len(minimal_bases)}

    report = {}
    old8 = json.loads((ROOT / 'results/2026-10-08-clift109-checks.json').read_text())
    old17 = json.loads((ROOT / 'results/2026-10-17-integration-checks.json').read_text())

    # all bases Mersenne: the 256 standard orientations (Lean minimum 110)
    every = family({v: 0 for v in INTER}, ())
    require(every['labellings'] == old8['standard_orientations'] == 256, 'standard count')
    require(every['histogram'] == old8['standard_cost_histogram'], 'standard histogram')
    report['all_mersenne'] = every

    # every base a shifted Mersenne (Lean minimum 109)
    best = None
    for L, lows, shapes in particulars:
        if all(shapes[v] == (1 << v) - 1 for v in INTER):
            value = min_cost(L)[0]
            best = value if best is None else min(best, value)
    require(best == 109, 'shifted-Mersenne minimum differs from Lean')
    report['all_shifted_mersenne_minimum'] = best

    # 8 October: only bases 5 and 7 free
    two = family({v: 0 for v in INTER if v not in (5, 7)}, (5, 7))
    require(two['base_assignments'] == len(old8['viable_base_pairs']) == 63, 'two-exception pairs')
    require(two['labellings'] == old8['complete_labellings_modulo_parallel_edge_swap'],
            'two-exception labellings')
    require(two['histogram'] == old8['two_exception_cost_histogram'], 'two-exception histogram')
    report['two_exception'] = two

    # 9 October: bases 5, 7 and one or two others free (36 cases)
    others = [v for v in INTER if v not in (5, 7)]
    stored = {tuple(c['additional_free_vertices']): c for c in old17['clift109_neighborhood']['cases']}
    require(len(stored) == 36, 'stored neighborhood cases')
    neighborhood = {}
    for extra, case in sorted(stored.items()):
        free = tuple(sorted((5, 7) + extra))
        got = family({v: 0 for v in others if v not in extra}, free)
        require(got['base_assignments'] == case['viable_base_assignments'], f'{extra} bases')
        require(got['labellings'] == case['labellings_modulo_parallel_swap'], f'{extra} labellings')
        require(got['histogram'] == case['cost_histogram'], f'{extra} histogram')
        require(got['minimum'] == case['minimum_doublings'], f'{extra} minimum')
        neighborhood[','.join(map(str, extra))] = {k: got[k] for k in
                                                     ('base_assignments', 'labellings', 'minimum')}
    report['neighborhood'] = neighborhood

    # 14 October: six early bases free, tails 23, 28, 51, 58 Mersenne
    early = old17['clift109_early']
    six = family({23: 0, 28: 0, 51: 0, 58: 0}, (2, 4, 5, 7, 8, 15))
    require(six['base_assignments'] == early['viable_base_assignments'], 'early bases')
    require(six['labellings'] == early['labellings_modulo_parallel_swap'], 'early labellings')
    require(six['histogram'] == early['cost_histogram'], 'early histogram')
    require(six['bases_at_110'] == early['distinct_minimizing_base_assignments'], 'early minima')
    report['six_early'] = six

    # 16 October: B58 = M58 fixed, B51 = M51*2^k and B7 = M7*2^l
    old16 = json.loads((ROOT / 'results/2026-10-16-clift109-fixed58.json').read_text())
    expected = {(c['k'], c['l']): c for c in old16['cases']}
    pairs = {}
    for (k, l), case in sorted(expected.items()):
        bases, best = set(), None
        for L, fixed, lows, shapes in restricted({58: 0, 51: k, 7: l}):
            r = min_cost(L, fixed)
            if r is None:
                continue
            best = r[0] if best is None else min(best, r[0])
            for g in feasible_points(L, fixed):
                bases.add(tuple(shapes[v] << (lows[v] + g[v]) for v in (2, 4, 5, 8, 15, 23, 28)))
        require(len(bases) == case['viable_base_assignments'], f'fixed58 {k},{l} count')
        require(case['budget_108_excluded'], 'stored fixed58 case not excluded')
        require((best == 109) == bool(case['witness_109']), f'fixed58 {k},{l} witness')
        pairs[f'{k},{l}'] = {'base_assignments': len(bases), 'minimum': best}
    report['fixed58'] = pairs
    report['fixed58_total_base_assignments'] = sum(v['base_assignments'] for v in pairs.values())
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seed', type=int, default=20261018)
    parser.add_argument('--random-tests', type=int, default=3000)
    args = parser.parse_args()
    with args.output.open('x') as handle:
        handle.write('{}\n')
    start = time.perf_counter()
    provenance = json.loads((ROOT / 'data/2026-10-08-clift109-source.json').read_text())
    require(provenance['source'] == SOURCE and provenance['selected_parents'] ==
            [list(pair) for pair in PARENTS], 'primary graph transcription differs')
    require(hashlib.sha256((ROOT / 'data/2026-10-08-clift109.png').read_bytes()).hexdigest()
            == provenance['diagram_sha256'], 'primary diagram hash differs')
    paths = [Path(__file__), ROOT / 'scripts/clift109_box_search.cpp',
             ROOT / 'scripts/clift109_box_dual.py', ROOT / 'scripts/experiment_clift109.py',
             ROOT / 'scripts/check_certificate.py',
             ROOT / 'results/2026-10-16-clift109-fixed58.json']
    report = {'started_at_australia_sydney': datetime.now(ZoneInfo('Australia/Sydney')).isoformat(),
              'python': platform.python_version(), 'seed': args.seed,
              'arithmetic': 'exact integers; standard library',
              'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in paths},
              'source': SOURCE, 'selected_parents': PARENTS}
    t = time.perf_counter()
    report['random_model_tests'] = random_model_tests(args.seed, args.random_tests)
    report['random_model_seconds'] = round(time.perf_counter() - t, 6)
    with tempfile.TemporaryDirectory() as tmp:
        configs, cpp_stats = run_cpp(Path(tmp))
    report['cpp_enumeration'] = cpp_stats
    t = time.perf_counter()
    dual, dual_stats = clift109_box_dual.search()
    dual_stats['seconds'] = round(time.perf_counter() - t, 6)
    report['independent_python_enumeration'] = dual_stats
    require(configs == dual, 'independent enumerations differ')
    require(len(configs) == len(set(configs)), 'duplicate configurations')
    report['configurations'] = [list(c) for c in configs]
    # every known labelling lies in the enumeration
    known = known_witness_tests()
    cfgset = set(configs)
    for L in known['standard'] + [known['fixed58_109']]:
        cfg, orient, flip = invariants(L)
        u, v, w, d1, d2, d3 = cfg[:6]
        key = (u, v, min(w, d3), d1, d2, max(w, d3)) + cfg[6:]
        require(key in cfgset, 'known interval labelling missing from enumeration')
    t = time.perf_counter()
    cases, histogram, critical, minimal = analyse(configs)
    report['cost_seconds'] = round(time.perf_counter() - t, 6)
    report['cases'] = len(cases)
    report['budget_108_feasible_cases'] = 0
    report['minimum_cost_histogram'] = dict(sorted(histogram.items()))
    report['minimum_doublings'] = min(histogram)
    report['critical_paths'] = {'-'.join(map(str, k)): n for k, n in critical.most_common()}
    # replay every 109 minimum through the existing independent checker
    replayed = set()
    for case in minimal:
        M = {v: tuple(case['optimal_shifts'][i]) for i, v in enumerate(VERTS[1:])}
        M = canonical_parallel(M)
        key = tuple(M[v] for v in VERTS[1:])
        if key in replayed:
            continue
        replayed.add(key)
        S = weight_sets(M)
        bases = [sum(1 << x for x in S[v]) for v in VERTS]
        labels = [M[SOURCE[i]] for i in range(1, len(SOURCE))]
        document = check_allocation(bases, labels)
        require(document['additions'] == 120, 'minimum allocation length')
    report['replayed_109_allocations'] = len(replayed)
    report['minimal_cases'] = [{k: c[k] for k in ('configuration', 'swap_w_d3', 'orientation',
                                                   'critical_path', 'optimal_shifts')}
                               for c in minimal]
    report['case_records'] = cases
    t = time.perf_counter()
    report['cross_checks'] = cross_checks(configs)
    report['cross_check_seconds'] = round(time.perf_counter() - t, 6)
    report['claim_boundary'] = (
        'Computational exclusion of budget 108 for every labelling of the selected 109 graph, '
        'with exact minimum 109. Enumeration completeness rests on the documented reductions '
        'and two independent programs; the negative cycles and flows certify each enumerated '
        'case. Not a Lean theorem, Scholz instance, optimal source or Mersenne-chain optimum.')
    report['runtime_seconds'] = round(time.perf_counter() - start, 6)
    args.output.write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps({k: report[k] for k in ('cases', 'budget_108_feasible_cases',
                                             'minimum_doublings', 'replayed_109_allocations',
                                             'runtime_seconds')}))


if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    main()
