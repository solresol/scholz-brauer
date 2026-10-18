#!/usr/bin/env python3
"""Reference model of the run-generalised Clift graph G(a,b,c), pure Python.

G(1,0,0) is Clift's selected 109 graph; G(5,9,3) is chain 9 of the optimal
27-step chains for 5784689. Everything here is independent of the C++ search
`clift5784689_loss_search.cpp` and is used to validate it:

* `graph`: vertices, selected parents and values;
* `config_losses`: the nine-component loss decomposition of a configuration;
* `random_saturated`: labellings with a prescribed critical path (all path
  edges carry their tail caps, every other vertex has zero out-shifts), whose
  atoms are read off by explicit path enumeration;
* `Reference`: the bottom-up loss enumeration (no cap pruning), a slow but
  simple second implementation for small graphs;
* `budget_check`: for a configuration, every role choice and orientation, the
  particular labelling, an exact interval test with big-integer bitsets, its
  critical path and the cost-(n-1) difference system (Bellman-Ford).

Standard library only.
"""
import itertools

U, V, W, F, G = 1, 2, 4, 8, 16
CLASS_NAMES = {U: 'U', V: 'v', W: 'W', F: 'F', G: 'G'}
# (name, base atoms, classes): see clift5784689_loss_search.cpp
COMPONENTS = [('box', ('t',), 31), ('eK', ('A1',), 27), ('ep', ('A1', 'p'), 3),
              ('eq', ('A1', 'q'), 19), ('tK', ('A2',), 25), ('tp', ('A2', 'p'), 1),
              ('zK', ('A3',), 24), ('zp', ('A3', 'p'), 0), ('zq', ('A3', 'q'), 16)]
ATOMS = ('t', 'A1', 'A2', 'A3', 'p', 'q')


def graph(a, b, c):
    """Vertex names in chain order, parents (first, second) and values."""
    names = ['R%d' % i for i in range(a + 1)]
    par = {}
    for i in range(1, a + 1):
        par['R%d' % i] = ('R%d' % (i - 1),) * 2
    two = 'R%d' % a
    par.update({'4': (two, two), '5': ('4', 'R0'), '7': ('5', two), '8': ('4', '4'),
                '15': ('8', '7'), 'F0': ('15', '8')})
    names += ['4', '5', '7', '8', '15', 'F0']
    for j in range(1, b + 1):
        par['F%d' % j] = ('F%d' % (j - 1),) * 2
        names.append('F%d' % j)
    fb = 'F%d' % b
    par.update({'28': (fb, '5'), 'G0': ('28', fb)})
    names += ['28', 'G0']
    for j in range(1, c + 1):
        par['G%d' % j] = ('G%d' % (j - 1),) * 2
        names.append('G%d' % j)
    gc = 'G%d' % c
    par.update({'58': (gc, '7'), 'S': ('58', gc)})
    names += ['58', 'S']
    val = {'R0': 1}
    for v in names[1:]:
        val[v] = val[par[v][0]] + val[par[v][1]]
    return names, par, val


def capacities(a, b, c):
    return {U: a, V: 1, W: 2, F: b + 1, G: c + 1}


def subset_sums(xs):
    s = [0]
    for e in xs:
        s = s + [y + e for y in s]
    return s


def config_losses(atoms, diffs):
    """Sorted loss multiset of a configuration (atoms dict, [(value, class)])."""
    cls = lambda m: [e for e, k in diffs if k & m]
    K, Kp = subset_sums(cls(F | G)), subset_sums(cls(G))
    R65 = K + [atoms['p']] + [atoms['q'] + y for y in Kp]
    R97 = K + [atoms['p']]
    out = [atoms['t'] + y for y in subset_sums(cls(31))]
    out += [atoms['A1'] + x + y for x in subset_sums(cls(U | V)) for y in R65]
    out += [atoms['A2'] + x + y for x in subset_sums(cls(U)) for y in R97]
    out += [atoms['A3'] + y for y in R65]
    return sorted(out)


# ------------------------------------------------------- explicit labellings

def all_paths(names, par):
    P = {'R0': [[]]}
    for v in names[1:]:
        P[v] = [p + [(v, k)] for k in (0, 1) for p in P[par[v][k]]]
    return P['S']


FAMILIES = [(X, i2, i1) for X in range(3) for i2 in range(2) for i1 in range(2)]


def critical_path(a, b, c, fam):
    """Vertices of the candidate critical path for family (X, i2, i1)."""
    X, i2, i1 = fam
    pi = ['R%d' % i for i in range(a + 1)] + ['4']
    pi += {0: ['8', '15'], 1: ['8'], 2: ['5', '7', '15']}[X]
    pi += ['F%d' % j for j in range(b + 1)] + (['28'] if i2 else [])
    pi += ['G%d' % j for j in range(c + 1)] + (['58'] if i1 else []) + ['S']
    return pi


def random_saturated(a, b, c, fam, rng, scale):
    """Random labelling saturating the given critical path."""
    names, par, _ = graph(a, b, c)
    pi = critical_path(a, b, c, fam)
    on = set(pi)
    pedges = set()
    for x, y in zip(pi, pi[1:]):
        pedges.add((y, [k for k in (0, 1) if par[y][k] == x][0]))
    cap = {x: rng.randrange(scale) for x in pi[:-1]}
    L = {}
    for v in names[1:]:
        s = []
        for k in (0, 1):
            t = par[v][k]
            if (v, k) in pedges:
                s.append(cap[t])
            elif t in on:
                s.append(rng.randrange(cap[t] + 1))
            else:
                s.append(0)
        L[v] = tuple(s)
    return names, par, L, sum(cap.values())


def atoms_of_labelling(names, par, L, C, a, b, c):
    """Configuration atoms (loss coordinates, loss = C - weight) by enumeration."""
    paths = all_paths(names, par)
    loss = lambda p: C - sum(L[v][k] for v, k in p)
    eps = [p for p in paths if ('5', 0) in p]
    at = {'t': min(loss(p) for p in paths if any(v == '8' for v, _ in p)),
          'A1': min(map(loss, eps)),
          'A2': min(loss(p) for p in paths if ('7', 1) in p),
          'A3': min(loss(p) for p in paths if ('5', 1) in p)}
    at['p'] = min(loss(p) for p in eps if ('58', 1) in p) - at['A1']
    at['q'] = min(loss(p) for p in eps if ('28', 1) in p) - at['A1']
    d = lambda v: abs(L[v][0] - L[v][1])
    diffs = [(d('R%d' % i), U) for i in range(1, a + 1)] + [(d('4'), V), (d('8'), W)]
    diffs.append((abs(L['15'][0] + L['F0'][0] - L['F0'][1]), W))
    diffs += [(d('F%d' % j), F) for j in range(1, b + 1)]
    diffs.append((abs(L['28'][0] + L['G0'][0] - L['G0'][1]), F))
    diffs += [(d('G%d' % j), G) for j in range(1, c + 1)]
    diffs.append((abs(L['58'][0] + L['S'][0] - L['S'][1]), G))
    return at, diffs, sorted(loss(p) for p in paths)


def atoms_by_dp(names, par, L, C, a, b, c):
    """Atoms of a saturated labelling from longest-path dynamic programming
    (no path enumeration; for large graphs). Same definitions as
    `atoms_of_labelling`: each atom is C minus a maximum path weight."""
    pre = {'R0': 0}
    for v in names[1:]:
        pre[v] = max(pre[par[v][k]] + L[v][k] for k in (0, 1))
    suf = {v: None for v in names}
    suf['S'] = 0
    children = {}
    for v in names[1:]:
        for k in (0, 1):
            children.setdefault(par[v][k], []).append((v, k))
    for u in reversed(names[:-1]):
        suf[u] = max(L[v][k] + suf[v] for v, k in children[u])
    two = 'R%d' % a
    best_eps = pre['4'] + L['5'][0] + suf['5']
    at = {'t': C - (pre['8'] + suf['8']),
          'A1': C - best_eps,
          'A2': C - (pre[two] + L['7'][1] + suf['7']),
          'A3': C - (L['5'][1] + suf['5'])}
    at['p'] = C - (pre['4'] + L['5'][0] + L['7'][0] + L['58'][1] + suf['58']) - at['A1']
    at['q'] = C - (pre['4'] + L['5'][0] + L['28'][1] + suf['28']) - at['A1']
    d = lambda v: abs(L[v][0] - L[v][1])
    diffs = [(d('R%d' % i), U) for i in range(1, a + 1)] + [(d('4'), V), (d('8'), W)]
    diffs.append((abs(L['15'][0] + L['F0'][0] - L['F0'][1]), W))
    diffs += [(d('F%d' % j), F) for j in range(1, b + 1)]
    diffs.append((abs(L['28'][0] + L['G0'][0] - L['G0'][1]), F))
    diffs += [(d('G%d' % j), G) for j in range(1, c + 1)]
    diffs.append((abs(L['58'][0] + L['S'][0] - L['S'][1]), G))
    return at, diffs


def minimal_element(atoms, diffs, item):
    """Smallest loss of the atom `item` (a name, or a (value, class) difference)."""
    bases = [('t', 31), ('A1', 27), ('A2', 25), ('A3', 24)]
    if item in ('t', 'A1', 'A2', 'A3'):
        return atoms[item]
    if item == 'p':
        return min(atoms['A1'], atoms['A2'], atoms['A3']) + atoms['p']
    if item == 'q':
        return min(atoms['A1'], atoms['A3']) + atoms['q']
    e, m = item
    return min(atoms[b] for b, mask in bases if mask & m) + e


# ------------------------------------------------------ reference search ---

class Reference:
    """Bottom-up enumeration of anchored configurations, no cap pruning.

    Losses as Python integer bitsets. The smallest uncovered loss x is the
    minimal element of a new atom; classes are lazy blocks of the partition
    induced by the active components, refined (by branching) on activation.
    """

    def __init__(self, a, b, c, anchor):
        self.n = graph(a, b, c)[2]['S']
        self.cap = capacities(a, b, c)
        self.ndiffs = sum(self.cap.values())
        self.anchor = anchor
        self.solutions = []
        self.nodes = 0

    def blocks(self, atoms):
        sig = {}
        for cl in (U, V, W, F, G):
            key = tuple(bool(m & cl) for _, base, m in COMPONENTS
                        if all(atoms[x] is not None for x in base))
            sig[key] = sig.get(key, 0) | cl
        return list(sig.values())

    def capok(self, diffs, blocks):
        return all(sum(1 for _, m in diffs if m == B) <= sum(self.cap[k] for k in self.cap if k & B)
                   for B in blocks)

    def run(self):
        atoms = dict.fromkeys(ATOMS)
        atoms[self.anchor] = 0
        self.activate(atoms, [], {}, 0)
        return self.solutions

    def activate(self, atoms, diffs, comps, covered):
        newc = [cp for cp in COMPONENTS if cp[0] not in comps
                and all(atoms[x] is not None for x in cp[1])]
        blocks = self.blocks(atoms)
        for pick in itertools.product(*[[B for B in blocks if B & m] for _, m in diffs]):
            nd = [(e, B) for (e, _), B in zip(diffs, pick)]
            if not self.capok(nd, blocks):
                continue
            cv, nc, ok = covered, dict(comps), True
            for name, base, m in newc:
                s = 1 << sum(atoms[x] for x in base)
                for e, B in nd:
                    if B & m:
                        s |= s << e
                if s >> self.n or s & cv:
                    ok = False
                    break
                cv |= s
                nc[name] = s
            if ok:
                self.step(atoms, nd, nc, cv)

    def step(self, atoms, diffs, comps, covered):
        self.nodes += 1
        full = (1 << self.n) - 1
        if covered == full:
            if len(diffs) != self.ndiffs or any(v is None for v in atoms.values()):
                raise RuntimeError('full cover with unknown atoms')
            self.solutions.append((dict(atoms), sorted(diffs)))
            return
        unc = ~covered & full
        x = (unc & -unc).bit_length() - 1
        for B in ('t', 'A1', 'A2', 'A3'):
            if atoms[B] is None:
                self.activate(dict(atoms, **{B: x}), diffs, comps, covered)
        known = [atoms[k] for k in ('A1', 'A2', 'A3') if atoms[k] is not None]
        if atoms['p'] is None and known:
            self.activate(dict(atoms, p=x - min(known)), diffs, comps, covered)
        known = [atoms[k] for k in ('A1', 'A3') if atoms[k] is not None]
        if atoms['q'] is None and known:
            self.activate(dict(atoms, q=x - min(known)), diffs, comps, covered)
        for B in self.blocks(atoms):
            if sum(1 for _, m in diffs if m == B) >= sum(self.cap[k] for k in self.cap if k & B):
                continue
            bases = [sum(atoms[z] for z in base) for name, base, m in COMPONENTS
                     if name in comps and m & B]
            if not bases:
                continue
            e = x - min(bases)
            cv, nc, ok = covered, dict(comps), True
            for name, base, m in COMPONENTS:
                if name in comps and m & B:
                    s = comps[name] << e
                    if s >> self.n or s & cv:
                        ok = False
                        break
                    cv |= s
                    nc[name] = comps[name] | s
            if ok:
                self.step(atoms, diffs + [(e, B)], nc, cv)


# ------------------------------------------------------ cost-(n-1) check ---

def to_weight(n, atoms, diffs):
    """Weight-coordinate configuration (reflection loss -> n-1-loss)."""
    cl = {k: sorted(e for e, m in diffs if m == k) for k in (U, V, W, F, G)}
    SK = sum(cl[F]) + sum(cl[G])
    SU = sum(cl[U])
    v, = cl[V]
    tot = SU + v + sum(cl[W]) + SK
    w = {'t': n - 1 - tot - atoms['t'], 'A1': n - 1 - SU - v - SK - atoms['A1'],
         'A2': n - 1 - SU - SK - atoms['A2'], 'A3': n - 1 - SK - atoms['A3'],
         'p': SK - atoms['p'], 'q': sum(cl[F]) - atoms['q']}
    return w, cl


def particular(a, b, c, w, Us, v, ww, d3, Fs, d2, Gs, d1, o):
    """A labelling (shifts may be negative) with the given weight configuration."""
    o1, o2, o3 = o
    L = {'R%d' % i: (Us[i - 1], 0) for i in range(1, a + 1)}
    L.update({'4': (v, 0), '5': (w['A1'], w['A3']), '7': (0, w['A2']), '8': (ww + w['t'], w['t']),
              '15': (0 if o3 else d3, 0), 'F0': (0, d3 if o3 else 0),
              '28': (0 if o2 else d2, w['q']), 'G0': (0, d2 if o2 else 0),
              '58': (0 if o1 else d1, w['p']), 'S': (0, d1 if o1 else 0)})
    L.update({'F%d' % j: (Fs[j - 1], 0) for j in range(1, b + 1)})
    L.update({'G%d' % j: (Gs[j - 1], 0) for j in range(1, c + 1)})
    return L


def weight_sets(names, par, L):
    """S_v as (offset, bits); None if two paths to some vertex share a weight."""
    S = {'R0': (0, 1)}
    for v in names[1:]:
        (oa, ba), (ob, bb) = S[par[v][0]], S[par[v][1]]
        xa, xb = oa + L[v][0], ob + L[v][1]
        off = min(xa, xb)
        ca, cb = ba << (xa - off), bb << (xb - off)
        if ca & cb:
            return None
        S[v] = (off, ca | cb)
    return S


def bellman_ford(cons, nodes):
    dist = dict.fromkeys(nodes, 0)
    for _ in range(len(nodes) + 1):
        changed = False
        for x, y, cst in cons:  # g_x - g_y <= cst
            if dist[y] + cst < dist[x]:
                dist[x] = dist[y] + cst
                changed = True
        if not changed:
            return dist
    return None


def budget_labelling(names, par, n, L, S):
    """Cost-(n-1) gauge of L (critical-path constraints), or None if infeasible."""
    top = {v: S[v][0] + S[v][1].bit_length() - 1 for v in names}
    path, v, target = [], 'S', n - 1
    while v != 'R0':
        hits = [k for k in (0, 1) if top[par[v][k]] + L[v][k] == target]
        if len(hits) != 1:
            raise ValueError('maximum path not unique')
        k = hits[0]
        path.append((v, k))
        target -= L[v][k]
        v = par[v][k]
    if target != 0:
        raise ValueError('critical path weight')
    on = set(path)
    tails = {par[v][k] for v, k in path}
    edges = [(v, k) for v in names[1:] for k in (0, 1)]
    children = {}
    for v, k in edges:
        children.setdefault(par[v][k], []).append((v, k))
    node = lambda x: 'Z' if x in ('R0', 'S') else x
    cons = []
    for v, k in edges:
        t = par[v][k]
        cons.append((node(t), node(v), L[v][k]))       # shift >= 0
        if t not in tails:
            cons.append((node(v), node(t), -L[v][k]))  # shift <= 0 off the path
    for t in tails:
        (vp, kp), = [e for e in children[t] if e in on]
        for v, k in children[t]:
            if (v, k) != (vp, kp):                      # path edge dominates
                cons.append((node(v), node(vp), L[vp][kp] - L[v][k]))
    inter = [x for x in names if x not in ('R0', 'S')]
    dist = bellman_ford(cons, ['Z'] + inter)
    if dist is None:
        return None
    g = {x: dist[node(x)] - dist['Z'] for x in names}
    return {v: tuple(L[v][k] + g[v] - g[par[v][k]] for k in (0, 1)) for v in names[1:]}


def replay(names, par, n, M):
    """Big-integer bases of a labelling; returns its cost if B_n = 2^n-1."""
    B = {'R0': 1}
    caps = {}
    for v in names[1:]:
        if min(M[v]) < 0:
            raise ValueError('negative shift')
        x, y = B[par[v][0]] << M[v][0], B[par[v][1]] << M[v][1]
        if x & y:
            raise ValueError('carry')
        B[v] = x + y
        for k in (0, 1):
            caps[par[v][k]] = max(caps.get(par[v][k], 0), M[v][k])
    if B['S'] != (1 << n) - 1:
        raise ValueError('endpoint is not the Mersenne number')
    return sum(caps.values())


def budget_check(a, b, c, atoms, diffs):
    """Every role choice and orientation: interval test and cost-(n-1) system."""
    names, par, val = graph(a, b, c)
    n = val['S']
    w, cl = to_weight(n, atoms, diffs)
    out = {'interval': None, 'cases': 0, 'feasible': []}
    v, = cl[V]
    for iw in (0, 1):
        ww, d3 = cl[W][iw], cl[W][1 - iw]
        for i2, d2 in enumerate(cl[F]):
            Fr = cl[F][:i2] + cl[F][i2 + 1:]
            for i1, d1 in enumerate(cl[G]):
                Gr = cl[G][:i1] + cl[G][i1 + 1:]
                for i0, u0 in enumerate(cl[U]):
                    Ur = [u0] + cl[U][:i0] + cl[U][i0 + 1:]
                    for o in itertools.product((0, 1), repeat=3):
                        L = particular(a, b, c, w, Ur, v, ww, d3, Fr, d2, Gr, d1, o)
                        S = weight_sets(names, par, L)
                        ok = S is not None and S['S'][0] == 0 and S['S'][1] == (1 << n) - 1
                        if out['interval'] is None:
                            out['interval'] = ok
                        if ok != out['interval']:
                            raise ValueError('interval status depends on roles')
                        if not ok:
                            return out
                        out['cases'] += 1
                        M = budget_labelling(names, par, n, L, S)
                        if M is not None:
                            if replay(names, par, n, M) != n - 1:
                                raise ValueError('budget labelling has the wrong cost')
                            out['feasible'].append({'roles': [iw, d2, d1, u0, list(o)],
                                                    'shifts': {k: list(s) for k, s in M.items()}})
    return out
