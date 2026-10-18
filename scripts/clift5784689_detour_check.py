#!/usr/bin/env python3
"""Independent validation for scripts/clift5784689_detour_search.cpp.

Subcommands (standard library only; run as `uv run scripts/clift5784689_detour_check.py ...`):

  validate  Enumerate every parent graph of every addition chain with sink
            n <= --max-n and at most --max-steps steps in which every vertex is
            an ancestor of the sink.  For each, enumerate ALL labellings with
            B(n) = 2^n - 1 and cost n - 1 by brute force (no detour or
            critical-path theory), run the C++ search on the same graphs with
            --expand, and require the two sets of labellings to be identical.
            Every C++ labelling is also replayed with big integers.
  replay    Replay every labelling in C++ JSON outputs with big integers.
  combine   Merge the JSON outputs of the jobs of one split run, check that
            every job is present exactly once and that they agree on the tree
            above the split depth, and report the summed statistics.
  ablate    Consistency of the optional pruning rules: run the C++ search with
            its default rules and with rules switched off (--no-lookahead,
            --no-packing, --no-parity, --no-chord-units, all of them) on every
            graph with n <= --max-n, <= --max-steps steps, and on --abc
            triples; the sets of labellings (and "no labelling" results) must
            agree.  Larger than brute force allows; not independent of the core
            search, which `validate` checks against brute force.
  family    Check the (a,b,c) construction against data/2026-10-18-clift5784689-chains.json
            (chain 9 must be (5,9,3)) and Clift's 109 graph (1,0,0).

Brute force.  Shifts are assigned vertex by vertex.  W(v), the set of path
weights from the source to v, is kept as a bit mask (it equals B(v) while the
weights are distinct).  Pruning, each necessary for a budget-attaining
labelling of a graph whose vertices all reach the sink:
  * W(v) has no repeated weight: two source-to-v paths of equal weight extend
    by one common v-to-sink path to two sink paths of equal weight, but
    B(n) = 2^n - 1 has binary weight n, so the n sink weights are distinct;
  * every weight is <= n - 1 (weights only grow along a path, and the sink
    weights are 0..n-1);
  * the caps assigned so far sum to <= n - 1 (caps only grow; the final cost
    must be n - 1).
At the sink W(n) must be exactly {0..n-1}, i.e. B(n) = 2^n - 1, and the cost
is then rechecked to be n - 1.
"""
import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


# ------------------------------------------------------------- graphs ----

def build(pairs):
    """values, par (index pairs) from a list of (p, q) parent values."""
    values = [1]
    index = {1: 0}
    par = [None]
    for p, q in pairs:
        if p not in index or q not in index:
            raise ValueError('parent not in chain')
        v = p + q
        if v <= values[-1]:
            raise ValueError('not increasing')
        index[v] = len(values)
        values.append(v)
        par.append((index[p], index[q]))
    return values, par


def all_live(values, par):
    k = len(values) - 1
    live = [False] * (k + 1)
    live[k] = True
    for v in range(k, 0, -1):
        if live[v]:
            live[par[v][0]] = live[par[v][1]] = True
    return all(live)


def enumerate_graphs(max_n, max_steps):
    """Every parent graph (slot 0 = larger parent) of every addition chain
    1 = v0 < v1 < ... < vk = n with n <= max_n, k <= max_steps, all live."""
    out = []

    def rec(values, pairs):
        if len(values) > 1:
            vals, par = build(pairs)
            if all_live(vals, par):
                out.append(list(pairs))
        if len(values) - 1 >= max_steps:
            return
        last = values[-1]
        for i in range(len(values)):
            for j in range(i + 1):
                v = values[i] + values[j]
                if last < v <= max_n:
                    rec(values + [v], pairs + [(values[i], values[j])])

    rec([1], [])
    return out


# --------------------------------------------------------- brute force ----

def brute_force(pairs):
    """All labellings (tuple of (shift0, shift1) per vertex 1..k) with
    B(n) = 2^n - 1 and cost n - 1."""
    values, par = build(pairs)
    k = len(values) - 1
    n = values[-1]
    full = (1 << n) - 1
    W = [0] * (k + 1)
    W[0] = 1
    cap = [0] * (k + 1)
    sh = [None] * (k + 1)
    found = []

    def rec(h, cost):
        if h > k:
            if W[k] == full:
                caps = [0] * (k + 1)
                for v in range(1, k + 1):
                    for s in (0, 1):
                        caps[par[v][s]] = max(caps[par[v][s]], sh[v][s])
                if sum(caps) == n - 1:
                    found.append(tuple(sh[1:]))
            return
        p, q = par[h]
        for a in range(0, n - W[p].bit_length() + 1):
            cp_old = cap[p]
            cp_new = max(cp_old, a)
            cost1 = cost - cp_old + cp_new
            if cost1 > n - 1:
                break
            cap[p] = cp_new
            Wa = W[p] << a
            for b in range(0, n - W[q].bit_length() + 1):
                cq_old = cap[q]
                cq_new = max(cq_old, b)
                cost2 = cost1 - cq_old + cq_new
                if cost2 > n - 1:
                    break
                Wb = W[q] << b
                if Wa & Wb:
                    continue
                cap[q] = cq_new
                W[h] = Wa | Wb
                sh[h] = (a, b)
                rec(h + 1, cost2)
                cap[q] = cq_old
            cap[p] = cp_old
        W[h] = 0
        sh[h] = None

    rec(1, 0)
    return found


# -------------------------------------------------------------- replay ----

def replay(pairs, shifts):
    """Big-integer replay; returns None if valid, else a reason."""
    values, par = build(pairs)
    k = len(values) - 1
    n = values[-1]
    if len(shifts) != k:
        return 'wrong number of vertices'
    B = [1] + [0] * k
    caps = [0] * (k + 1)
    for h in range(1, k + 1):
        a, b = shifts[h - 1]
        if a < 0 or b < 0:
            return 'negative shift'
        B[h] = (B[par[h][0]] << a) + (B[par[h][1]] << b)
        caps[par[h][0]] = max(caps[par[h][0]], a)
        caps[par[h][1]] = max(caps[par[h][1]], b)
    if B[k] != (1 << n) - 1:
        return 'B(n) != 2^n - 1'
    if sum(caps) != n - 1:
        return 'cost != n - 1'
    return None


def pairs_of(result):
    return [tuple(p) for p in result['parents']]


def replay_result(result):
    """Replay every labelling of one C++ graph result. Returns (count, errors)."""
    pairs = pairs_of(result)
    count = 0
    errors = []
    for ps in result.get('pstars', []):
        for key in ('labellings', 'expanded'):
            for L in ps.get(key, []):
                count += 1
                why = replay(pairs, L)
                if why:
                    errors.append((ps['index'], key, L, why))
    return count, errors


# ------------------------------------------------------------ commands ----

def compile_cpp(out):
    src = ROOT / 'scripts' / 'clift5784689_detour_search.cpp'
    cmd = ['c++', '-O2', '-std=c++17', '-Wall', '-Wextra', '-Werror', '-o', str(out), str(src)]
    subprocess.run(cmd, check=True)
    return cmd


def cmd_validate(args):
    t0 = time.time()
    scratch = Path(args.scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    binary = Path(args.binary) if args.binary else scratch / 'detour_validate'
    if not args.binary:
        compile_cpp(binary)
    graphs = enumerate_graphs(args.max_n, args.max_steps)
    print(f'{len(graphs)} live parent graphs with n <= {args.max_n}, <= {args.max_steps} steps', flush=True)
    batch = scratch / 'validate_batch.txt'
    batch.write_text(''.join(','.join(f'{p}+{q}' for p, q in g) + '\n' for g in graphs))
    t1 = time.time()
    proc = subprocess.run([str(binary), '--batch', str(batch), '--expand', '--no-describe',
                           '--max-labellings', '100000000'], check=True, capture_output=True, text=True)
    cpp_seconds = time.time() - t1
    cpp = [json.loads(line) for line in proc.stdout.splitlines() if line.strip()]
    if len(cpp) != len(graphs):
        sys.exit(f'C++ returned {len(cpp)} results for {len(graphs)} graphs')
    t2 = time.time()
    mismatches = []
    positive = 0
    total_lab = 0
    replayed = 0
    by_n = {}
    for g, r in zip(graphs, cpp):
        if 'error' in r:
            mismatches.append((g, 'C++ error ' + r['error']))
            continue
        if pairs_of(r) != g:
            mismatches.append((g, 'C++ parsed a different graph'))
            continue
        if r.get('truncated'):
            mismatches.append((g, 'C++ output truncated'))
            continue
        bf = brute_force(g)
        bfset = set(bf)
        if len(bfset) != len(bf):
            mismatches.append((g, 'brute force repeated a labelling'))
        cset = set()
        for ps in r['pstars']:
            for L in ps.get('expanded', []):
                cset.add(tuple(tuple(x) for x in L))
        if len(cset) != r['total_expanded_labellings']:
            mismatches.append((g, 'C++ expanded list has repeats'))
        c, errs = replay_result(r)
        replayed += c
        if errs:
            mismatches.append((g, f'{len(errs)} C++ labellings fail big-integer replay'))
        if cset != bfset:
            mismatches.append((g, f'brute force {len(bfset)} vs C++ {len(cset)} labellings; '
                                  f'only brute {sorted(bfset - cset)[:3]}, only C++ {sorted(cset - bfset)[:3]}'))
        n = r['n']
        st = by_n.setdefault(n, [0, 0, 0])
        st[0] += 1
        if bfset:
            positive += 1
            st[1] += 1
        st[2] += len(bfset)
        total_lab += len(bfset)
    py_seconds = time.time() - t2
    summary = {
        'max_n': args.max_n, 'max_steps': args.max_steps, 'graphs': len(graphs),
        'graphs_with_labellings': positive, 'graphs_without': len(graphs) - positive,
        'labellings_total': total_lab, 'cpp_labellings_replayed': replayed,
        'mismatches': len(mismatches), 'cpp_seconds': round(cpp_seconds, 2),
        'brute_force_and_compare_seconds': round(py_seconds, 2),
        'total_seconds': round(time.time() - t0, 2),
        'by_n': {str(k): {'graphs': v[0], 'positive': v[1], 'labellings': v[2]} for k, v in sorted(by_n.items())},
    }
    print(json.dumps(summary, indent=1))
    for g, why in mismatches[:20]:
        print('MISMATCH', g, why)
    if args.output:
        Path(args.output).write_text(json.dumps({'summary': summary, 'mismatches': [[g, w] for g, w in mismatches]},
                                                indent=1))
    if mismatches:
        sys.exit(1)


def load_results(paths):
    out = []
    for p in paths:
        for line in Path(p).read_text().splitlines():
            if line.strip():
                out.append((p, json.loads(line)))
    return out


def cmd_replay(args):
    bad = 0
    total = 0
    for path, r in load_results(args.files):
        if 'error' in r:
            print(path, 'ERROR', r['error'])
            bad += 1
            continue
        c, errs = replay_result(r)
        total += c
        found = sum(len(ps.get('labellings', [])) for ps in r['pstars'])
        if found:
            print(f'*** {path}: n={r["n"]}: {found} LABELLING(S) FOUND ***')
            for ps in r['pstars']:
                for L in ps.get('labellings', []):
                    print('   P*', ps['index'], json.dumps(L))
        for e in errs:
            print(path, 'REPLAY FAILURE', e)
            bad += 1
        print(f'{path}: n={r["n"]} result={r["result"]} labellings replayed={c} failures={len(errs)}')
    print(f'replayed {total} labellings, {bad} failures')
    if bad:
        sys.exit(1)


def run_splits(r):
    """Split levels of a run: [[depth, jobs, job], ...] (older single-level form too)."""
    if r.get('splits') is not None:
        return [tuple(x) for x in r['splits']]
    return [(r['split_depth'], r['jobs'], r['job'])] if r['jobs'] > 1 else []


def split_complete(runs, level=0):
    """None if the runs form exactly one complete job set from `level` on,
    else a description of the problem."""
    deeper = [r for r in runs if len(r[0]) > level]
    if not deeper:
        return None if len(runs) == 1 else f'{len(runs)} runs duplicate the same work'
    if len(deeper) != len(runs):
        return 'mixed split structures'
    dj = {(sp[level][0], sp[level][1]) for sp, _ in runs}
    if len(dj) != 1:
        return f'different splits at level {level}: {sorted(dj)}'
    D, J = dj.pop()
    for j in range(J):
        sub = [x for x in runs if x[0][level][2] == j]
        if not sub:
            return f'missing job {j} of {J} at depth {D}'
        why = split_complete(sub, level + 1)
        if why:
            return f'job {j}/{J} at depth {D}: {why}'
    return None


def cmd_combine(args):
    """Merge result files of one graph.  Each file is one C++ run (all P* or
    --pstar I), possibly one job of a (hierarchically) split run.  For every
    critical path, the runs covering it must have the same scope (set of P*
    they cover, since split numbering runs over that scope) and form exactly
    one complete job set; all P* 0..num_pstars-1 must be covered."""
    res = load_results(args.files)
    if not res:
        sys.exit('no results')
    for path, r in res:
        if 'error' in r:
            sys.exit(f'{path}: error {r["error"]}')
    keys = {(tuple(r['values']), tuple(map(tuple, r['parents']))) for _, r in res}
    if len(keys) != 1:
        sys.exit('results are for different graphs')
    num = {r['num_pstars'] for _, r in res}
    if len(num) != 1:
        sys.exit('inconsistent num_pstars')
    num = num.pop()
    groups = {}
    for path, r in res:
        scope = tuple(ps['index'] for ps in r['pstars'])
        for ps in r['pstars']:
            groups.setdefault(ps['index'], []).append((path, r, ps, scope))
    per = {}
    labs = []
    problems = []
    for i in range(num):
        g = groups.get(i, [])
        if not g:
            problems.append(f'P*{i} not covered')
            continue
        if len({sc for _, _, _, sc in g}) != 1:
            problems.append(f'P*{i} covered by runs with different scopes')
            continue
        why = split_complete([(run_splits(r), path) for path, r, _, _ in g])
        if why:
            problems.append(f'P*{i}: {why}')
            continue
        d = {'runs': len(g), 'nodes': 0, 'leaves': 0, 'feasible_systems': 0,
             'labellings': 0, 'truncated': False, 'rejected': None,
             'job_seconds_sum': 0.0, 'job_seconds_max': 0.0}
        for _, r, ps, _ in g:
            for key in ('nodes', 'leaves', 'feasible_systems'):
                d[key] += ps[key]
            d['labellings'] += len(ps['labellings'])
            d['truncated'] = d['truncated'] or ps['truncated']
            d['rejected'] = ps.get('rejected')
            d['job_seconds_sum'] = round(d['job_seconds_sum'] + ps['seconds'], 1)
            d['job_seconds_max'] = round(max(d['job_seconds_max'], ps['seconds']), 1)
            labs.extend((i, L) for L in ps['labellings'])
        per[i] = d
    incomplete = problems or any(d['truncated'] for d in per.values())
    summary = {
        'n': res[0][1]['n'], 'num_pstars': num, 'covered_pstars': sorted(per),
        'problems': problems,
        'total_nodes': sum(d['nodes'] for d in per.values()),
        'total_labellings': len(labs),
        'result': 'labellings found' if labs else ('incomplete' if incomplete else 'no labelling'),
        'per_pstar': per,
    }
    print(json.dumps(summary, indent=1))
    for i, L in labs:
        print('*** LABELLING FOUND on P*', i, json.dumps(L))
    if args.output:
        Path(args.output).write_text(json.dumps(summary, indent=1))
    if problems:
        sys.exit(1)


ABLATIONS = [
    ('no-lookahead', ['--no-lookahead']),
    ('no-packing', ['--no-packing']),
    ('no-parity', ['--no-parity']),
    ('no-chord-units', ['--no-chord-units']),
    ('minimal', ['--no-lookahead', '--no-packing', '--no-parity', '--no-chord-units']),
]


def labelling_set(r):
    out = set()
    for ps in r['pstars']:
        for L in ps['labellings']:
            out.add(tuple(tuple(x) for x in L))
    return out


def cmd_ablate(args):
    t0 = time.time()
    scratch = Path(args.scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    binary = Path(args.binary)
    specs = []
    if args.max_n:
        specs += [','.join(f'{p}+{q}' for p, q in g) for g in enumerate_graphs(args.max_n, args.max_steps)]
    for t in args.abc or []:
        a, b, c = (int(x) for x in t.split(','))
        specs.append(','.join(f'{p}+{q}' for p, q in abc_pairs(a, b, c)))
    batch = scratch / 'ablate_batch.txt'
    batch.write_text(''.join(sp + '\n' for sp in specs))
    common = ['--batch', str(batch), '--no-describe', '--max-labellings', str(args.max_labellings)]
    runs = {}
    for name, flags in [('default', [])] + ABLATIONS:
        t1 = time.time()
        proc = subprocess.run([str(binary)] + common + flags, check=True, capture_output=True, text=True)
        runs[name] = [json.loads(line) for line in proc.stdout.splitlines() if line.strip()]
        nodes = sum(r.get('total_nodes', 0) for r in runs[name])
        print(f'{name}: {len(runs[name])} graphs, {nodes} nodes, {time.time() - t1:.1f} s', flush=True)
    bad = []
    compared = skipped = positive = 0
    for i, sp in enumerate(specs):
        rs = {k: v[i] for k, v in runs.items()}
        if any('error' in r for r in rs.values()):
            bad.append((sp, 'error'))
            continue
        if any(r['truncated'] for r in rs.values()):
            skipped += 1
            continue
        ref = labelling_set(rs['default'])
        positive += bool(ref)
        for k, r in rs.items():
            if labelling_set(r) != ref or r['result'] != rs['default']['result']:
                bad.append((sp, k))
        compared += 1
    summary = {'graphs': len(specs), 'compared': compared, 'skipped_truncated': skipped,
               'compared_with_labellings': positive, 'disagreements': len(bad),
               'seconds': round(time.time() - t0, 1),
               'nodes': {k: sum(r.get('total_nodes', 0) for r in v) for k, v in runs.items()}}
    print(json.dumps(summary, indent=1))
    for sp, k in bad[:20]:
        print('DISAGREE', k, sp)
    if args.output:
        Path(args.output).write_text(json.dumps({'summary': summary, 'disagreements': bad}, indent=1))
    if bad:
        sys.exit(1)


def abc_pairs(a, b, c):
    """The spec's chain for (a, b, c), as (p, q) value pairs."""
    pairs = []
    R = 1
    for _ in range(a):
        pairs.append((R, R))
        R *= 2
    v4 = 2 * R
    pairs.append((R, R))
    v5 = v4 + 1
    pairs.append((v4, 1))
    v7 = v5 + R
    pairs.append((v5, R))
    v8 = 2 * v4
    pairs.append((v4, v4))
    v15 = v8 + v7
    pairs.append((v8, v7))
    F = v15 + v8
    pairs.append((v15, v8))
    for _ in range(b):
        pairs.append((F, F))
        F *= 2
    v28 = F + v5
    pairs.append((F, v5))
    G = v28 + F
    pairs.append((v28, F))
    for _ in range(c):
        pairs.append((G, G))
        G *= 2
    v58 = G + v7
    pairs.append((G, v7))
    pairs.append((v58, G))
    return pairs


def cmd_family(args):
    data = json.loads((ROOT / 'data' / '2026-10-18-clift5784689-chains.json').read_text())
    chain9 = data['chains'][8]
    vals, par = build(abc_pairs(5, 9, 3))
    ok = vals == chain9
    print('(5,9,3) values equal chain 9 of the JSON:', ok, '; n =', vals[-1], '; steps =', len(vals) - 1)
    # parent selection of chain 9: every value must have exactly one decomposition into earlier values
    amb = []
    for i, v in enumerate(chain9[1:], 1):
        dec = [(chain9[x], chain9[y]) for x in range(i) for y in range(x + 1) if chain9[x] + chain9[y] == v]
        if len(dec) != 1:
            amb.append((v, dec))
    print('chain 9 values with a non-unique parent pair:', amb)
    mine = [(vals[p], vals[q]) for p, q in par[1:]]
    unique = []
    for i, v in enumerate(chain9[1:], 1):
        dec = [(chain9[x], chain9[y]) for x in range(i) for y in range(x + 1) if chain9[x] + chain9[y] == v]
        unique.append(dec[0] if dec else None)
    agree = all(u is not None and set(m) == set(u) for m, u in zip(mine, unique))
    print('(5,9,3) parent pairs equal the unique decompositions of chain 9:', agree)
    v109, p109 = build(abc_pairs(1, 0, 0))
    print('(1,0,0) values:', v109)
    ok109 = v109 == [1, 2, 4, 5, 7, 8, 15, 23, 28, 51, 58, 109]
    print('(1,0,0) equals Clift selected 109 vertex list:', ok109)
    if not (ok and agree and ok109 and not amb):
        sys.exit(1)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    v = sub.add_parser('validate')
    v.add_argument('--max-n', type=int, default=12)
    v.add_argument('--max-steps', type=int, default=6)
    v.add_argument('--scratch', required=True)
    v.add_argument('--binary')
    v.add_argument('--output')
    r = sub.add_parser('replay')
    r.add_argument('files', nargs='+')
    c = sub.add_parser('combine')
    c.add_argument('files', nargs='+')
    c.add_argument('--output')
    ab = sub.add_parser('ablate')
    ab.add_argument('--binary', required=True)
    ab.add_argument('--scratch', required=True)
    ab.add_argument('--max-n', type=int, default=0)
    ab.add_argument('--max-steps', type=int, default=7)
    ab.add_argument('--abc', action='append')
    ab.add_argument('--max-labellings', type=int, default=20000)
    ab.add_argument('--output')
    sub.add_parser('family')
    args = ap.parse_args()
    {'validate': cmd_validate, 'replay': cmd_replay, 'combine': cmd_combine, 'family': cmd_family,
     'ablate': cmd_ablate}[args.cmd](args)


if __name__ == '__main__':
    main()
