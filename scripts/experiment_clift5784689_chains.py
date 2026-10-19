#!/usr/bin/env python3
"""Labellability of the other 15 optimal chains of 5784689 (chains 1-8, 10-16).

All 16 optimal chains are run-generalised Clift graphs G(a,s,b,c) with chord
variants (vX, vY, vZ) (`clift5784689_reference.graph`): chains 1-8 are
G(4,10,0,4) and chains 9-16 are G(5,1,9,3), with variant = binary(k-1) and
binary(k-9). The nine-component loss decomposition is the same in every case;
only the critical paths and their cap constraints change. This driver

1. checks every chain of the data file against its G(a,s,b,c) variant;
2. tests the loss decomposition and the caps test of the C++ search against
   random critical-path-saturated labellings of random small variants and of
   all 16 chain graphs;
3. compares the C++ enumeration without caps pruning with the Python
   reference for small graphs with s > 1, and checks every configuration
   found by the explicit cost-(n-1) system under all eight variants;
4. positive control with variants and s > 1 (constraint groups dropped);
   the same with the option halve=all (halving test for every class), and the
   enumeration without caps pruning is unchanged by that option;
5. summarises the completed chain runs of `clift5784689_parallel.py` (search
   directories c<k>_<anchor>) and of the independent detour search
   (`clift5784689_detour_search.cpp`, one JSON per job).

Exact integers, standard library, recorded seed. Computational result.
"""
import argparse
from collections import Counter
from datetime import datetime
import glob
import hashlib
import itertools
import json
import os
from pathlib import Path
import platform
import random
import subprocess
import sys
import time
from zoneinfo import ZoneInfo

import clift5784689_reference as ref
import experiment_clift5784689 as base
from clift5784689_parallel import summarise

ROOT = Path(__file__).resolve().parents[1]
CHAINS = ROOT / 'data/2026-10-18-clift5784689-chains.json'
VARIANTS = [(x, y, z) for x in (0, 1) for y in (0, 1) for z in (0, 1)]


def require(cond, message):
    if not cond:
        raise ValueError(message)


def chain_params(k):
    """(a, b, c, s, variant) of chain k (1..16)."""
    if k <= 8:
        return 4, 0, 4, 10, VARIANTS[k - 1]
    return 5, 9, 3, 1, VARIANTS[k - 9]


def vflag(var):
    return '%d%d%d' % var


def opts(var, s):
    return (['var=' + vflag(var)] if var != (0, 0, 0) else []) + (['s=%d' % s] if s != 1 else [])


def lptest(binary, a, b, c, s, var, queries, env=None):
    lines = []
    for n, x, atoms, diffs in queries:
        A = [atoms[k] if atoms[k] is not None else -1 for k in ref.ATOMS]
        lines.append('%d %d %s %d %s' % (n, x, ' '.join(map(str, A)), len(diffs),
                                         ' '.join('%d:%d' % d for d in diffs)))
    r = subprocess.run([binary, str(a), str(b), str(c), 'lptest'] + opts(var, s),
                       input='\n'.join(lines) + '\n', capture_output=True, text=True, check=True, env=env)
    out = r.stdout.split()
    require(len(out) == len(queries), 'lptest output length')
    return [o == '1' for o in out]


def run_cpp(binary, a, b, c, s, var, anchor, out, extra=(), env=None):
    return base.run_cpp(binary, a, b, c, anchor, out, list(extra) + opts(var, s), env=env)


def provenance():
    data = json.loads(CHAINS.read_text())
    out = {}
    for k in range(1, 17):
        a, b, c, s, var = chain_params(k)
        chain = data['chains'][k - 1]
        names, par, val = ref.graph(a, b, c, var, s)
        require([val[v] for v in names] == chain, 'chain %d is not its G(a,s,b,c) variant' % k)
        for i, x in enumerate(chain[1:], 1):
            pairs = [(chain[p], chain[q]) for p in range(i) for q in range(p, i) if chain[p] + chain[q] == x]
            v = names[i]
            require(pairs == [tuple(sorted((val[par[v][0]], val[par[v][1]])))], 'parent of %d in chain %d' % (x, k))
        out[str(k)] = {'a': a, 'b': b, 'c': c, 's': s, 'variant': vflag(var),
                       'critical_path_families': len(ref.families(var))}
    return out


def random_tests(binary, rng, count):
    """Decomposition, anchors and caps acceptance on random small variants."""
    stats = Counter()
    queries = {}
    while stats['labellings'] < count:
        a, b, c, s = rng.randrange(1, 4), rng.randrange(0, 3), rng.randrange(0, 2), rng.randrange(1, 4)
        var = rng.choice(VARIANTS)
        if ref.graph(a, b, c, var, s)[2]['S'] > 1600:
            continue
        fam = rng.choice(ref.families(var))
        names, par, L, C = ref.random_saturated(a, b, c, fam, rng, rng.choice([8, 30, 200, 1000]), s)
        at, diffs, losses = ref.atoms_of_labelling(names, par, L, C, a, b, c)
        require(ref.config_losses(at, diffs) == losses, 'loss decomposition differs from paths')
        require(ref.atoms_by_dp(names, par, L, C, a, b, c) == (at, diffs), 'DP atoms differ')
        anchor = 'A1' if fam[0] == 2 else 't'
        require(at[anchor] == 0, 'anchor is not the critical path')
        stats['labellings'] += 1
        if at['A1' if anchor == 't' else 't'] <= 0 or min(at['p'], at['q']) <= 0 or min(e for e, _ in diffs) <= 0:
            continue
        stats['caps_eligible'] += 1
        for hp in (0.15, 0.4, 0.7):
            queries.setdefault((a, b, c, s, var), []).append(relaxed_query(rng, at, diffs, anchor, C, hp))
    for (a, b, c, s, var), qs in queries.items():
        require(all(lptest(binary, a, b, c, s, var, qs)), 'CAPS TEST REJECTS A SATURATED LABELLING')
        stats['caps_queries_accepted'] += len(qs)
    return dict(stats)


def relaxed_query(rng, at, diffs, anchor, C, hp):
    items = list(ref.ATOMS) + list(range(len(diffs)))
    hide = [it for it in items if it != anchor and rng.random() < hp]
    mins = [ref.minimal_element(at, diffs, diffs[it] if isinstance(it, int) else it) for it in hide]
    x = rng.randint(0, min(mins)) if mins else rng.randint(0, C + 1)
    atoms = {k: (None if k in hide else at[k]) for k in ref.ATOMS}
    ds = [(e, m | rng.randrange(32) if rng.random() < 0.3 else m) for i, (e, m) in enumerate(diffs) if i not in hide]
    return (C + 1, x, atoms, ds)


def chain_graph_tests(binary, rng, count):
    """Caps acceptance on saturated labellings of every chain graph itself."""
    out = {}
    for k in range(1, 17):
        a, b, c, s, var = chain_params(k)
        qs = []
        while len(qs) < count:
            fam = rng.choice(ref.families(var))
            names, par, L, C = ref.random_saturated(a, b, c, fam, rng, rng.choice([30, 1000, 10 ** 5]), s)
            at, diffs = ref.atoms_by_dp(names, par, L, C, a, b, c)
            anchor = 'A1' if fam[0] == 2 else 't'
            require(at[anchor] == 0, 'anchor is not the critical path')
            if at['A1' if anchor == 't' else 't'] <= 0 or min(at['p'], at['q']) <= 0 or min(e for e, _ in diffs) <= 0:
                continue
            qs.append(relaxed_query(rng, at, diffs, anchor, C, rng.choice([0.15, 0.4, 0.7])))
        require(all(lptest(binary, a, b, c, s, var, qs)), 'CAPS TEST REJECTS A LABELLING OF CHAIN %d' % k)
        out[str(k)] = len(qs)
    return out


SMALL_S = [(1, 0, 0, 2), (1, 0, 0, 3), (2, 0, 0, 2)]


def reference_and_leaves(binary, workdir, small_s=SMALL_S):
    """C++ without caps equals the Python reference (s > 1); every configuration
    of these and of the five s = 1 graphs fails under all eight variants."""
    out = {}
    for (a, b, c, s) in small_s:
        cfgs = []
        for anchor in ('t', 'A1'):
            t0 = time.perf_counter()
            R = ref.Reference(a, b, c, anchor, s)
            py = sorted(base.key((at, sorted(d))) for at, d in R.run())
            _, got = run_cpp(binary, a, b, c, s, (0, 0, 0), anchor, Path(workdir) / 'nolp.txt', ['nolp'])
            require(py == sorted(base.key(x) for x in got), 'reference differs at %s' % ((a, b, c, s),))
            cfgs += got
            out['%d,%d,%d,s%d,%s' % (a, b, c, s, anchor)] = {'configurations': len(py),
                                                              'reference_seconds': round(time.perf_counter() - t0, 1)}
        out['%d,%d,%d,s%d' % (a, b, c, s)] = leaf_checks(a, b, c, s, cfgs)
    for (a, b, c) in base.SMALL:
        cfgs = []
        for anchor in ('t', 'A1'):
            _, got = run_cpp(binary, a, b, c, 1, (0, 0, 0), anchor, Path(workdir) / 'nolp.txt', ['nolp'])
            cfgs += got
        out['%d,%d,%d,s1' % (a, b, c)] = leaf_checks(a, b, c, 1, cfgs)
    return out


def leaf_checks(a, b, c, s, cfgs):
    res = {}
    for var in VARIANTS:
        feas = 0
        for at, d in cfgs:
            chk = ref.budget_check(a, b, c, at, d, var, s)
            require(chk['interval'], 'configuration is not an interval labelling')
            feas += bool(chk['feasible'])
        require(feas == 0, 'COST n-1 LABELLING FOUND at %s variant %s' % ((a, b, c, s), var))
        res[vflag(var)] = 0
    return {'configurations': len(cfgs), 'labellings_by_variant': res}


def positive_control(binary, workdir, extras=([], ['halve=all'])):
    out = []
    for (a, b, c, s) in [(1, 0, 0, 2), (2, 0, 0, 1), (1, 1, 0, 1)]:
        n = ref.graph(a, b, c, (0, 0, 0), s)[2]['S']
        for var in [(0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 1)]:
            for anchor in ('t', 'A1'):
                if anchor == 'A1' and var[0]:
                    continue
                _, cfgs = run_cpp(binary, a, b, c, s, (0, 0, 0), anchor, Path(workdir) / 'pc.txt', ['nolp'])
                for mask in (1, 2, 4, 8, 16, 32, 6):
                    env = dict(os.environ, LPDROP=str(mask))
                    acc = lptest(binary, a, b, c, s, var, [(n, n, at, d) for at, d in cfgs], env=env) if cfgs else []
                    want = sorted(base.key(x) for x, ok in zip(cfgs, acc) if ok)
                    for extra in extras:
                        _, got = run_cpp(binary, a, b, c, s, var, anchor, Path(workdir) / 'pc2.txt', extra, env=env)
                        got = sorted(base.key(x) for x in got)
                        require(got == want, 'positive control failed at %s %s %s %d %s'
                                % ((a, b, c, s), var, anchor, mask, extra))
                        out.append({'graph': [a, b, c, s], 'variant': vflag(var), 'anchor': anchor, 'drop_mask': mask,
                                    'options': extra, 'leaf_accepted': len(want), 'search_found': len(got)})
    require(any(r['search_found'] for r in out), 'positive control never positive')
    return out


HALVING_CASES = [(1, 0, 0, 1, (0, 0, 0)), (2, 0, 0, 1, (0, 0, 0)), (1, 1, 0, 1, (0, 0, 0)), (1, 0, 1, 1, (0, 0, 0)),
                 (1, 0, 0, 2, (0, 0, 0)), (1, 0, 0, 3, (0, 0, 0)), (2, 0, 0, 2, (0, 0, 0)), (1, 0, 1, 2, (0, 1, 1)),
                 (1, 1, 0, 2, (0, 1, 0)), (1, 0, 0, 2, (1, 1, 1)), (2, 0, 1, 2, (1, 0, 1)), (2, 1, 1, 1, (0, 0, 0))]


def halving_tests(binary, workdir):
    """The option halve=all only prunes: without caps pruning it returns the
    same configurations (every exact cover passes the halving test)."""
    out = {}
    for (a, b, c, s, var) in HALVING_CASES:
        for anchor in ('t', 'A1'):
            if anchor == 'A1' and var[0]:
                continue
            st0, c0 = run_cpp(binary, a, b, c, s, var, anchor, Path(workdir) / 'h0.txt', ['nolp'])
            st1, c1 = run_cpp(binary, a, b, c, s, var, anchor, Path(workdir) / 'h1.txt', ['nolp', 'halve=all'])
            require(st1['halve_all'] == 1 and st0['halve_all'] == 0, 'halve option not applied')
            require(sorted(base.key(x) for x in c0) == sorted(base.key(x) for x in c1),
                    'HALVING TEST CHANGES THE CONFIGURATIONS at %s' % ((a, b, c, s, var, anchor),))
            out['%d,%d,%d,s%d,%s,%s' % (a, b, c, s, vflag(var), anchor)] = {
                'configurations': len(c0), 'nodes': st0['nodes'], 'nodes_halve_all': st1['nodes']}
    require(sum(v['configurations'] for v in out.values()) > 0, 'halving tests saw no configuration')
    return out


def chain_runs(rundirs, rng, chains):
    """Summaries of the completed loss-coordinate searches of the given chains."""
    out = {}
    for k in chains:
        a, b, c, s, var = chain_params(k)
        for anchor in ('t', 'A1'):
            if anchor == 'A1' and var[0]:
                continue  # no critical path through 4-5-7 when "16" = 2*"8"
            wd = None
            for d in rundirs:
                if (Path(d) / ('c%d_%s' % (k, anchor)) / 'records.jsonl').exists():
                    wd = Path(d) / ('c%d_%s' % (k, anchor))
            require(wd is not None, 'no run directory for chain %d %s' % (k, anchor))
            # options.json is written by the driver; older runs used the defaults
            extra = json.loads((wd / 'options.json').read_text())['extra'] if (wd / 'options.json').exists() \
                else opts(var, s)
            require(extra[:len(opts(var, s))] == opts(var, s) and extra[len(opts(var, s)):] in ([], ['halve=all']),
                    'unexpected options for chain %d %s' % (k, anchor))
            recs = {}
            for line in (wd / 'records.jsonl').read_text().splitlines():
                r = json.loads(line)
                recs[r['id']] = r
            s_ = summarise(recs, wd)
            require(s_['configurations'] == [], 'CONFIGURATION SURVIVES IN CHAIN %d: inspect' % k)
            splits = []
            for rid, r in sorted(recs.items()):
                if r['kind'] != 'split':
                    continue
                kids = ['%s.%d' % (rid, j) for j in range(r['children'])]
                run_kids = [recs[x] for x in kids if recs[x]['kind'] == 'run']
                splits.append({'id': rid, 'nodes': r['nodes'], 'jobs': r['jobs'], 'children': r['children'],
                               'split_children': [x for x in kids if recs[x]['kind'] == 'split'],
                               'run_children': len(run_kids),
                               'run_children_nodes': sum(x['nodes'] for x in run_kids),
                               'configurations': len(r['configurations']) + sum(len(x['configurations']) for x in run_kids)})
            runs = sorted((rid, r['nodes']) for rid, r in recs.items() if r['kind'] == 'run')
            small = [x for x in runs if x[0].count('.') == 1 and x[1] <= 3000]
            canon = ''.join(json.dumps([rid, r['kind'], r['nodes'], r.get('jobs', 0), len(r['configurations'])]) + '\n'
                            for rid, r in sorted(recs.items()))
            out['%d,%s' % (k, anchor)] = {
                'chain': k, 'anchor': anchor, 'variant': vflag(var), 's': s, 'options': extra, 'nodes': s_['nodes'],
                'configurations': s_['configurations'], 'job_runs': s_['job_runs'], 'splits': s_['splits'],
                'longest_job_seconds': s_['longest_job_seconds'],
                'job_seconds_total': round(sum(r.get('seconds', 0) for r in recs.values()), 1),
                'split_records': splits, 'replay_sample': rng.sample(small, min(60, len(small))),
                'records_canonical_sha256': hashlib.sha256(canon.encode()).hexdigest(),
                'root_jobs_sha256': base.sha256(wd / 'root.jobs')}
    return out


def detour_runs(dirs, pstars, chains):
    """Coverage and outcome of the independent detour search jobs per chain."""
    files = {}
    for d in dirs:
        for f in glob.glob(os.path.join(d, 'c*_p*.json')):
            files[os.path.basename(f)] = f
    out = {}
    want = {('14:3:1',), ('14:3:2',)} | {('14:3:0', '20:4:%d' % j) for j in range(4)}
    for k in chains:
        jobs, seen = [], {}
        for name, f in sorted(files.items()):
            if not name.startswith('c%d_p' % k):
                continue
            d = json.loads(Path(f).read_text())
            require(len(d['pstars']) == 1, 'detour job covers several critical paths')
            p = d['pstars'][0]
            nodes = p['nodes']
            ok = (d['result'] == 'no labelling' and not d['truncated'] and p['leaves'] == 0
                  and p['feasible_systems'] == 0 and d['total_canonical_labellings'] == 0)
            require(ok, 'DETOUR JOB %s IS NOT A CLEAN EXCLUSION' % name)
            seen.setdefault(p['index'], set()).add(tuple('%d:%d:%d' % tuple(x) for x in d['splits']))
            jobs.append({'file': name, 'pstar': p['index'], 'splits': d['splits'], 'nodes': nodes,
                         'rejected': p.get('rejected'), 'seconds': round(d['seconds'], 1),
                         'sha256': base.sha256(f)})
        require(sorted(seen) == list(range(pstars[k])), 'detour chain %d: critical paths missing' % k)
        for i, v in seen.items():
            rej = [j for j in jobs if j['pstar'] == i and j['rejected']]
            require(v == want or (rej and v == {()}), 'detour chain %d P*%d: incomplete job set' % (k, i))
        out[str(k)] = {'critical_paths': pstars[k], 'rejected': sorted({j['pstar'] for j in jobs if j['rejected']}),
                       'jobs': jobs, 'nodes': sum(j['nodes'] for j in jobs),
                       'cpu_seconds': round(sum(j['seconds'] for j in jobs), 1), 'result': 'no labelling'}
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--workdir', type=Path, required=True)
    ap.add_argument('--runs', type=Path, nargs='+', required=True, help='directories holding c<k>_<anchor>')
    ap.add_argument('--detour', type=Path, nargs='+', required=True, help='directories of detour job JSONs')
    ap.add_argument('--seed', type=int, default=20261020)
    ap.add_argument('--samples', type=int, default=3000)
    ap.add_argument('--chain-list', default='1,2,3,4,5,6,7,8,10,11,12,13,14,15,16')
    ap.add_argument('--small-s', default='1,0,0,2;1,0,0,3;2,0,0,2',
                    help='graphs a,b,c,s with s > 1 for the reference comparison (empty: none)')
    args = ap.parse_args()
    with args.output.open('x') as fh:
        fh.write('{}\n')
    started = datetime.now(ZoneInfo('Australia/Sydney'))
    t_all = time.perf_counter()
    args.workdir.mkdir(parents=True, exist_ok=True)
    srcs = [Path(__file__), ROOT / 'scripts/clift5784689_loss_search.cpp', ROOT / 'scripts/clift5784689_reference.py',
            ROOT / 'scripts/clift5784689_parallel.py', ROOT / 'scripts/experiment_clift5784689.py',
            ROOT / 'scripts/clift5784689_detour_search.cpp', ROOT / 'scripts/clift5784689_detour_check.py', CHAINS]
    report = {'started_at_australia_sydney': started.isoformat(), 'python': platform.python_version(),
              'seed': args.seed, 'arithmetic': 'exact integers; standard library',
              'input_sha256': {str(p.relative_to(ROOT)): base.sha256(p) for p in srcs}}
    binary, version = base.compile_search(args.workdir)
    report['compiler'] = version
    report['flags'] = base.FLAGS
    timings = {}

    def timed(name, f, *a):
        t0 = time.perf_counter()
        r = f(*a)
        timings[name] = round(time.perf_counter() - t0, 1)
        print(name, 'done', timings[name], flush=True)
        return r

    rng = random.Random(args.seed)
    report['chains'] = timed('provenance', provenance)
    report['random_tests'] = timed('random', random_tests, binary, rng, args.samples)
    report['chain_graph_caps_tests'] = timed('chain_graphs', chain_graph_tests, binary, rng, 400)
    small_s = [tuple(map(int, x.split(','))) for x in args.small_s.split(';') if x]
    report['reference_and_leaf_checks'] = timed('reference', reference_and_leaves, binary, args.workdir, small_s)
    report['positive_control'] = timed('control', positive_control, binary, args.workdir)
    report['halving_all_tests'] = timed('halving', halving_tests, binary, args.workdir)
    chains = [int(x) for x in args.chain_list.split(',')]
    report['chain_list'] = chains
    report['chain_runs'] = timed('runs', chain_runs, args.runs, rng, chains)
    pstars = {k: 0 for k in range(1, 17)}
    for k in pstars:
        pstars[k] = len(ref.families(chain_params(k)[4]))
    # the detour program also lists critical paths it rejects outright
    pstars.update({1: 14, 2: 7})
    report['detour_runs'] = timed('detour', detour_runs, [str(d) for d in args.detour], pstars, chains)
    report['timings_seconds'] = timings
    report['claim_boundary'] = (
        'Computational exclusion, chain by chain, of cost-(n-1) labellings of the listed optimal 27-step chains '
        'for 5784689 (chain 9: 2026-10-19 report), by two independently written complete searches. '
        'Not a Lean theorem; no statement about other chains for 2^5784689-1 or about Scholz-Brauer at 5784689.')
    report['runtime_seconds'] = round(time.perf_counter() - t_all, 1)
    args.output.write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps({'timings_seconds': timings, 'runtime_seconds': report['runtime_seconds']}))


if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    main()
