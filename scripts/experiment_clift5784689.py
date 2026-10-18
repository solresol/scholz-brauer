#!/usr/bin/env python3
"""Labellability of chain 9 of Clift's optimal chains for 5784689.

Chain 9 is the run-generalised Clift graph G(5,9,3); Clift's selected 109 graph
is G(1,0,0). The question is whether some edge labelling has cap sum n-1, i.e.
B_n = 2^n-1 with n-1 doublings (Scholz at 5784689 via this chain).

This driver
1. checks the chain data against G(5,9,3) and G(1,0,0) against the 109 graph;
2. tests the loss decomposition and the caps test of the C++ search
   (`clift5784689_loss_search.cpp`) against random critical-path-saturated
   labellings (explicit path enumeration, `clift5784689_reference.py`);
3. compares the C++ enumeration without caps pruning with the independent
   Python reference enumeration, and with the 2026-10-18 109 box exclusion;
4. checks every configuration found without caps pruning by the explicit
   cost-(n-1) difference system (no labelling);
5. positive control: with constraint groups dropped, the pruned search finds
   exactly the configurations the dropped test accepts at the leaf;
6. runs the pruned search on a ladder of G(a,b,c) and on G(5,9,3) (parallel,
   checkpointed in --workdir; a completed run is only re-summarised).

Exact integers, standard library, recorded seed.  Computational result, not a
Lean theorem.
"""
import argparse
from collections import Counter
from datetime import datetime
import hashlib
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
from clift5784689_parallel import run_search

ROOT = Path(__file__).resolve().parents[1]
SOURCE_CPP = ROOT / 'scripts/clift5784689_loss_search.cpp'
CHAINS = ROOT / 'data/2026-10-18-clift5784689-chains.json'
BOX109 = ROOT / 'results/2026-10-18-clift109-box-exclusion.json'
FLAGS = ['-O2', '-std=c++17', '-Wall', '-Wextra', '-Werror']
SMALL = [(1, 0, 0), (2, 0, 0), (1, 1, 0), (1, 0, 1), (2, 1, 1)]
LADDER = [(1, 0, 0), (2, 0, 0), (1, 1, 0), (1, 0, 1), (2, 1, 1), (3, 0, 0), (5, 0, 0),
          (1, 9, 0), (1, 0, 3), (3, 3, 1), (5, 1, 1), (2, 2, 2), (5, 3, 1), (3, 5, 2)]


def require(cond, message):
    if not cond:
        raise ValueError(message)


def sha256(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def compile_search(workdir):
    binary = Path(workdir) / 'clift5784689_loss_search'
    subprocess.run(['c++'] + FLAGS + ['-o', str(binary), str(SOURCE_CPP)], check=True)
    version = subprocess.run(['c++', '--version'], capture_output=True, text=True).stdout.splitlines()[0]
    return str(binary), version


def run_cpp(binary, a, b, c, anchor, out, extra=(), env=None):
    out = Path(out)
    if out.exists():
        out.unlink()
    r = subprocess.run([binary, str(a), str(b), str(c), anchor, str(out)] + list(extra),
                       capture_output=True, text=True, check=True, env=env)
    stats = json.loads(r.stdout.splitlines()[-1])
    cfgs = [parse_config(l) for l in out.read_text().splitlines() if l.startswith('C')]
    out.unlink()
    return stats, cfgs


def parse_config(line):
    f = line.split()[1:]
    atoms = dict(zip(ref.ATOMS, map(int, f[:6])))
    diffs = sorted(tuple(map(int, x.split(':'))) for x in f[6:])
    return atoms, diffs


def key(cfg):
    atoms, diffs = cfg
    return tuple(atoms[k] for k in ref.ATOMS) + tuple(diffs)


def lptest(binary, a, b, c, queries, env=None):
    """queries: (n, x, atoms dict with None for unknown, [(value, mask)]) -> [bool]."""
    lines = []
    for n, x, atoms, diffs in queries:
        A = [atoms[k] if atoms[k] is not None else -1 for k in ref.ATOMS]
        lines.append('%d %d %s %d %s' % (n, x, ' '.join(map(str, A)), len(diffs),
                                         ' '.join('%d:%d' % d for d in diffs)))
    r = subprocess.run([binary, str(a), str(b), str(c), 'lptest'], input='\n'.join(lines) + '\n',
                       capture_output=True, text=True, check=True, env=env)
    out = r.stdout.split()
    require(len(out) == len(queries), 'lptest output length')
    return [o == '1' for o in out]


# ------------------------------------------------------------ checks -------

def provenance():
    data = json.loads(CHAINS.read_text())
    chain9 = data['chains'][8]
    names, par, val = ref.graph(5, 9, 3)
    require([val[v] for v in names] == chain9, 'chain 9 is not G(5,9,3)')
    for i, x in enumerate(chain9[1:], 1):
        pairs = [(chain9[p], chain9[q]) for p in range(i) for q in range(p, i) if chain9[p] + chain9[q] == x]
        v = names[i]
        require(pairs == [tuple(sorted((val[par[v][0]], val[par[v][1]])))], 'parent of %d' % x)
    names1, par1, val1 = ref.graph(1, 0, 0)
    source109 = [1, 2, 4, 5, 7, 8, 15, 23, 28, 51, 58, 109]
    require([val1[v] for v in names1] == source109, 'G(1,0,0) is not the 109 graph')
    return {'chain9': chain9, 'n': chain9[-1], 'steps': len(chain9) - 1,
            'graph_109_values': source109, 'unique_parent_pairs_checked': len(chain9) - 1}


def decomposition_and_lp_tests(binary, rng, count, hide_probs=(0.15, 0.4, 0.7)):
    """Random saturated labellings: loss decomposition, anchors, caps test acceptance."""
    stats = Counter()
    queries = {}
    while stats['labellings'] < count:
        a, b, c = rng.randrange(1, 5), rng.randrange(0, 4), rng.randrange(0, 3)
        if ref.graph(a, b, c)[2]['S'] > 1600:  # explicit path enumeration: keep graphs small
            continue
        fam = rng.choice(ref.FAMILIES)
        names, par, L, C = ref.random_saturated(a, b, c, fam, rng, rng.choice([8, 30, 200, 1000]))
        at, diffs, losses = ref.atoms_of_labelling(names, par, L, C, a, b, c)
        require(ref.config_losses(at, diffs) == losses, 'loss decomposition differs from paths')
        require(at['t' if fam[0] < 2 else 'A1'] == 0, 'anchor is not the critical path')
        require(min(at.values()) >= 0 and min(e for e, _ in diffs) >= 0, 'negative atom')
        stats['labellings'] += 1
        anchor = 't' if fam[0] < 2 else 'A1'
        ok_anchor = at['A1' if anchor == 't' else 't'] > 0
        if not ok_anchor or min(at['p'], at['q']) <= 0 or min(e for e, _ in diffs) <= 0:
            continue  # degenerate (equal losses): outside the search's domain
        stats['caps_eligible'] += 1
        for hp in hide_probs:
            items = list(ref.ATOMS) + list(range(len(diffs)))
            hide = [it for it in items if it != anchor and rng.random() < hp]
            mins = [ref.minimal_element(at, diffs, diffs[it] if isinstance(it, int) else it) for it in hide]
            x = rng.randint(0, min(mins)) if mins else rng.randint(0, C + 1)
            atoms = {k: (None if k in hide else at[k]) for k in ref.ATOMS}
            ds = []
            for i, (e, m) in enumerate(diffs):
                if i in hide:
                    continue
                ds.append((e, m | rng.randrange(32) if rng.random() < 0.3 else m))
            queries.setdefault((a, b, c), []).append((C + 1, x, atoms, ds))
    accepted = 0
    for (a, b, c), qs in queries.items():
        res = lptest(binary, a, b, c, qs)
        require(all(res), 'CAPS TEST REJECTS A SATURATED LABELLING at %s' % ((a, b, c),))
        accepted += len(res)
    stats['caps_queries_accepted'] = accepted
    return dict(stats)


def caps_tests_large(binary, rng, count, graphs=((5, 9, 3), (5, 5, 3), (3, 9, 1), (5, 3, 1))):
    """Caps-test acceptance of random saturated labellings of large graphs,
    including chain 9 itself; atoms by longest-path dynamic programming."""
    stats = Counter()
    for (a, b, c) in graphs:
        qs = []
        while len(qs) < count:
            fam = rng.choice(ref.FAMILIES)
            names, par, L, C = ref.random_saturated(a, b, c, fam, rng, rng.choice([30, 1000, 10 ** 5]))
            at, diffs = ref.atoms_by_dp(names, par, L, C, a, b, c)
            anchor = 't' if fam[0] < 2 else 'A1'
            require(at[anchor] == 0, 'anchor is not the critical path')
            if at['A1' if anchor == 't' else 't'] <= 0 or min(at['p'], at['q']) <= 0 or min(e for e, _ in diffs) <= 0:
                continue
            items = list(ref.ATOMS) + list(range(len(diffs)))
            hide = [it for it in items if it != anchor and rng.random() < rng.choice([0.15, 0.4, 0.7])]
            mins = [ref.minimal_element(at, diffs, diffs[it] if isinstance(it, int) else it) for it in hide]
            x = rng.randint(0, min(mins)) if mins else rng.randint(0, C + 1)
            atoms = {k: (None if k in hide else at[k]) for k in ref.ATOMS}
            ds = [(e, m | rng.randrange(32) if rng.random() < 0.3 else m)
                  for i, (e, m) in enumerate(diffs) if i not in hide]
            qs.append((C + 1, x, atoms, ds))
        res = lptest(binary, a, b, c, qs)
        require(all(res), 'CAPS TEST REJECTS A SATURATED LABELLING at %s' % ((a, b, c),))
        stats['%d,%d,%d' % (a, b, c)] = len(res)
    return dict(stats)


def reference_comparison(binary, workdir):
    """C++ without caps pruning equals the Python reference; leaf checks."""
    out = {}
    for (a, b, c) in SMALL:
        for anchor in ('t', 'A1'):
            t0 = time.perf_counter()
            R = ref.Reference(a, b, c, anchor)
            py = sorted(key((at, sorted(d))) for at, d in R.run())
            py_s = time.perf_counter() - t0
            stats, cfgs = run_cpp(binary, a, b, c, anchor, Path(workdir) / 'nolp.txt', ['nolp'])
            cpp = sorted(key(x) for x in cfgs)
            require(py == cpp, 'reference and C++ enumerations differ at %s %s' % ((a, b, c), anchor))
            feasible = 0
            for cfg in cfgs:
                chk = ref.budget_check(a, b, c, *cfg)
                require(chk['interval'], 'configuration is not an interval labelling')
                feasible += bool(chk['feasible'])
            require(feasible == 0, 'COST n-1 LABELLING FOUND at %s' % ((a, b, c),))
            out['%d,%d,%d,%s' % (a, b, c, anchor)] = {
                'configurations': len(cfgs), 'reference_nodes': R.nodes, 'reference_seconds': round(py_s, 3),
                'cpp_nodes_without_caps': stats['nodes'], 'cost_n_minus_1_labellings': feasible}
    return out


def box109_comparison(binary, workdir):
    """The 2026-10-18 enumeration of all 216 interval configurations of the 109
    graph, reflected to loss coordinates, restricted to anchored ones with
    positive atoms, equals this search's 48 configurations (without caps)."""
    box = json.loads(BOX109.read_text())
    want = set()
    for cfg in box['configurations']:
        u, v, w, d1, d2, d3, t, p, q, A1, A2, A3 = cfg
        L = {'t': 108 - t - (u + v + w + d1 + d2 + d3), 'A1': 108 - A1 - u - v - d1 - d2,
             'A2': 108 - A2 - u - d1 - d2, 'A3': 108 - A3 - d1 - d2, 'p': d1 + d2 - p, 'q': d2 - q}
        if (L['t'] == 0 or L['A1'] == 0) and min(L.values()) >= 0 and L['p'] > 0 and L['q'] > 0:
            want.add(key((L, sorted([(u, ref.U), (v, ref.V), (w, ref.W), (d3, ref.W), (d2, ref.F), (d1, ref.G)]))))
    got = set()
    for anchor in ('t', 'A1'):
        _, cfgs = run_cpp(binary, 1, 0, 0, anchor, Path(workdir) / 'box.txt', ['nolp'])
        got |= {key(x) for x in cfgs}
    require(got == want, 'differs from the 109 box enumeration')
    return {'box_configurations': len(box['configurations']), 'anchored_positive': len(want), 'equal': True}


def positive_control(binary, workdir):
    """Dropping constraint groups makes leaves feasible; the pruned search must
    return exactly the no-caps configurations accepted by the same test."""
    out = []
    for (a, b, c) in [(1, 0, 0), (2, 0, 0), (1, 1, 0), (1, 0, 1)]:
        n = ref.graph(a, b, c)[2]['S']
        for anchor in ('t', 'A1'):
            _, cfgs = run_cpp(binary, a, b, c, anchor, Path(workdir) / 'pc.txt', ['nolp'])
            for mask in (1, 2, 4, 8, 16, 32, 6, 24):
                env = dict(os.environ, LPDROP=str(mask))
                acc = lptest(binary, a, b, c, [(n, n, at, d) for at, d in cfgs], env=env) if cfgs else []
                want = sorted(key(x) for x, ok in zip(cfgs, acc) if ok)
                _, got = run_cpp(binary, a, b, c, anchor, Path(workdir) / 'pc2.txt', env=env)
                got = sorted(key(x) for x in got)
                require(got == want, 'positive control failed at %s %s mask %d' % ((a, b, c), anchor, mask))
                out.append({'graph': [a, b, c], 'anchor': anchor, 'drop_mask': mask,
                            'leaf_accepted': len(want), 'search_found': len(got)})
    require(any(r['search_found'] for r in out), 'positive control never positive')
    return out


def ladder(binary, workdir, workers):
    out = {}
    for (a, b, c) in LADDER:
        for anchor in ('t', 'A1'):
            t0 = time.perf_counter()
            s = run_search(binary, a, b, c, anchor, Path(workdir) / ('ladder_%d_%d_%d_%s' % (a, b, c, anchor)),
                           workers=workers, depth=8, step=3, timeout=600, log=lambda m: None)
            require(s['configurations'] == [], 'configuration survives at %s' % ((a, b, c),))
            out['%d,%d,%d,%s' % (a, b, c, anchor)] = {'nodes': s['nodes'], 'configurations': 0,
                                                      'job_runs': s['job_runs'],
                                                      'seconds': round(time.perf_counter() - t0, 1)}
    return out


def chain9(binary, workdir, workers, rng):
    """Run (or resume, or only re-summarise) the chain-9 search of both anchors.

    The job tree is stored compactly: every split record with the totals of
    its directly run children, plus a seeded sample of run records for replay
    and the hash of the complete record log (kept in the work directory)."""
    out = {}
    for anchor in ('t', 'A1'):
        t0 = time.perf_counter()
        wd = Path(workdir) / anchor
        s = run_search(binary, 5, 9, 3, anchor, wd, workers=workers, depth=10, step=3, timeout=300,
                       log=lambda m: print(m, flush=True), batch_size=64)
        recs = {}
        for line in (wd / 'records.jsonl').read_text().splitlines():
            r = json.loads(line)
            recs[r['id']] = r
        splits = []
        for rid, r in sorted(recs.items()):
            if r['kind'] != 'split':
                continue
            kids = ['%s.%d' % (rid, k) for k in range(r['children'])]
            run_kids = [recs[k] for k in kids if recs[k]['kind'] == 'run']
            splits.append({'id': rid, 'nodes': r['nodes'], 'jobs': r['jobs'], 'children': r['children'],
                           'split_children': [k for k in kids if recs[k]['kind'] == 'split'],
                           'run_children': len(run_kids),
                           'run_children_nodes': sum(k['nodes'] for k in run_kids),
                           'configurations': len(r['configurations']) + sum(len(k['configurations']) for k in run_kids)})
        runs = sorted((rid, r['nodes']) for rid, r in recs.items() if r['kind'] == 'run')
        small = [x for x in runs if x[0].count('.') == 1 and x[1] <= 3000]
        canon = ''.join(json.dumps([rid, r['kind'], r['nodes'], r.get('jobs', 0), len(r['configurations'])]) + '\n'
                        for rid, r in sorted(recs.items()))
        out[anchor] = {'nodes': s['nodes'], 'configurations': s['configurations'],
                       'job_runs': s['job_runs'], 'splits': s['splits'],
                       'longest_job_seconds': s['longest_job_seconds'],
                       'summary_seconds': round(time.perf_counter() - t0, 1),
                       'job_seconds_total': round(sum(r.get('seconds', 0) for r in recs.values()), 1),
                       'split_records': splits,
                       'replay_sample': rng.sample(small, min(200, len(small))),
                       'records_canonical_sha256': hashlib.sha256(canon.encode()).hexdigest(),
                       'root_jobs_sha256': sha256(wd / 'root.jobs')}
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--workdir', type=Path, required=True)
    ap.add_argument('--chain9-workdir', type=Path, required=True)
    ap.add_argument('--workers', type=int, default=3)
    ap.add_argument('--seed', type=int, default=20261019)
    ap.add_argument('--samples', type=int, default=4000)
    args = ap.parse_args()
    with args.output.open('x') as fh:
        fh.write('{}\n')
    started = datetime.now(ZoneInfo('Australia/Sydney'))
    t_all = time.perf_counter()
    args.workdir.mkdir(parents=True, exist_ok=True)
    report = {'started_at_australia_sydney': started.isoformat(), 'python': platform.python_version(),
              'seed': args.seed, 'arithmetic': 'exact integers; standard library',
              'input_sha256': {str(p.relative_to(ROOT)): sha256(p) for p in [
                  Path(__file__), SOURCE_CPP, ROOT / 'scripts/clift5784689_reference.py',
                  ROOT / 'scripts/clift5784689_parallel.py', CHAINS, BOX109]}}
    binary, version = compile_search(args.workdir)
    report['compiler'] = version
    report['flags'] = FLAGS
    timings = {}

    def timed(name, f, *a):
        t0 = time.perf_counter()
        r = f(*a)
        timings[name] = round(time.perf_counter() - t0, 1)
        print(name, 'done', timings[name], flush=True)
        return r

    report['provenance'] = timed('provenance', provenance)
    rng = random.Random(args.seed)
    report['decomposition_and_caps_tests'] = timed('random', decomposition_and_lp_tests, binary, rng, args.samples)
    report['caps_tests_large_graphs'] = timed('random_large', caps_tests_large, binary, rng, args.samples // 4)
    report['reference_comparison'] = timed('reference', reference_comparison, binary, args.workdir)
    report['box109_comparison'] = timed('box109', box109_comparison, binary, args.workdir)
    report['positive_control'] = timed('control', positive_control, binary, args.workdir)
    report['ladder'] = timed('ladder', ladder, binary, args.workdir, args.workers)
    report['chain9'] = timed('chain9', chain9, binary, args.chain9_workdir, args.workers, rng)
    for anchor in ('t', 'A1'):
        require(report['chain9'][anchor]['configurations'] == [], 'chain 9 configuration survives: inspect')
    report['timings_seconds'] = timings
    report['claim_boundary'] = (
        'Computational exclusion: no labelling of chain 9 (G(5,9,3)) of the optimal chains for 5784689 has '
        'cap sum 5784688, by a complete loss-coordinate enumeration with sound pruning, validated as recorded. '
        'Not a Lean theorem; says nothing about chains 1-8 or 10-16, about other addition chains for 2^5784689-1, '
        'or about the Scholz-Brauer conjecture at 5784689.')
    report['runtime_seconds'] = round(time.perf_counter() - t_all, 1)
    args.output.write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps({k: report[k] for k in ('timings_seconds', 'runtime_seconds')}))


if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    main()
