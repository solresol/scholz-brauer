#!/usr/bin/env python3
"""Check the saved chain-9 evidence of `experiment_clift5784689.py` (fast).

* structural checks of the report: every recorded configuration count is zero,
  every ladder and reference case is excluded, the positive control is positive;
* the chain-9 job tree is complete (every split has all its children) and its
  node totals add up exactly;
* fresh reruns: compile the C++ search; for G(1,0,0) compare its enumeration
  without caps pruning with the Python reference and check every configuration
  by the explicit cost-(n-1) system; a short random caps-soundness test; the
  chain-9 root splits must reproduce the stored job lists (hash), and a seeded
  sample of small chain-9 jobs must reproduce their stored node counts.

With `--chains` it checks the report of `experiment_clift5784689_chains.py` for
chains 1-8 and 10-16 in the same way: complete job trees, both root job lists
of every chain reproduced by hash, a seeded sample of jobs replayed (with the
search source and options recorded in the report), complete coverage of every
critical path by the detour jobs, and caps soundness on every chain graph.

With `--detour` it also checks the saved results of the independently written
detour-model search (`clift5784689_detour_search.cpp`): source hash, complete
job coverage of all 12 critical paths with no labelling, a fresh G(1,0,0) run,
a small brute-force comparison and one replayed chain-9 job.

It does not repeat the multi-hour searches; completeness is the experiments'
claim. Standard library only.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile

import clift5784689_reference as ref
import experiment_clift5784689 as exp


def fail(message):
    raise ValueError(message)


def tree_totals(c9):
    """Exact node total of the stored job tree (split records with the totals
    of their directly run children); every split child must be accounted for."""
    splits = {r['id']: r for r in c9['split_records']}
    if 'root' not in splits:
        fail('no root split')
    nodes, configs, runs, seen = 0, 0, 0, set()
    stack = ['root']
    while stack:
        rid = stack.pop()
        if rid in seen or rid not in splits:
            fail('split %s missing or repeated' % rid)
        seen.add(rid)
        r = splits[rid]
        if r['jobs'] != r['children'] or len(r['split_children']) + r['run_children'] != r['children']:
            fail('split %s children do not add up' % rid)
        for k in r['split_children']:
            if not k.startswith(rid + '.') or not 0 <= int(k.rsplit('.', 1)[1]) < r['children']:
                fail('bad child id %s' % k)
        nodes += r['nodes'] - r['jobs'] + r['run_children_nodes']
        runs += r['run_children']
        configs += r['configurations']
        stack.extend(r['split_children'])
    if seen != set(splits):
        fail('split records outside the job tree')
    return nodes, configs, runs


def check_detour(path, tmp):
    """Saved results of the independent detour-model search."""
    root = exp.ROOT
    rep = json.loads(Path(path).read_text())
    src = root / 'scripts/clift5784689_detour_search.cpp'
    chk = root / 'scripts/clift5784689_detour_check.py'
    for p in (src, chk):
        if hashlib.sha256(p.read_bytes()).hexdigest() != rep['source_sha256'][str(p.relative_to(root))]:
            fail('detour source changed: %s' % p.name)
    if rep['source_used_for_runs_sha256'] != rep['source_sha256']['scripts/clift5784689_detour_search.cpp']:
        fail('detour runs used another source')
    jobs = rep['chain9_jobs']
    want = {('14:3:1',), ('14:3:2',)} | {('14:3:0', '20:4:%d' % j) for j in range(4)}
    seen = {}
    for j in jobs:
        if j['result'] != 'no labelling' or j['leaves'] or j['labellings'] or j['feasible_systems'] or j['truncated']:
            fail('detour job %s is not a clean exclusion' % j['file'])
        if len(j['pstars']) != 1:
            fail('detour job covers several critical paths')
        seen.setdefault(j['pstars'][0], set()).add(tuple('%d:%d:%d' % tuple(x) for x in j['splits']))
    if sorted(seen) != list(range(12)) or any(v != want for v in seen.values()):
        fail('detour jobs do not cover every critical path completely')
    comb = rep['chain9_combined']
    if comb['result'] != 'no labelling' or comb['problems'] or comb['total_nodes'] != sum(j['nodes'] for j in jobs):
        fail('detour combined summary inconsistent')
    if any(v['result'] != 'no labelling' for v in rep['ladder'].values()):
        fail('detour ladder has a labelling')
    for k in ('brute_force_validation_n14_steps6', 'brute_force_validation_n18_steps5'):
        if rep[k]['mismatches'] != 0:
            fail('detour brute-force mismatch')
    binary = str(Path(tmp) / 'detour')
    subprocess.run(['c++'] + exp.FLAGS + ['-o', binary, str(src)], check=True)

    def run(args):
        r = subprocess.run([binary, '--no-describe'] + args, capture_output=True, text=True, check=True)
        return json.loads(r.stdout)

    g = run(['--abc', '1,0,0'])
    if g['result'] != 'no labelling' or g['total_nodes'] != rep['ladder']['1,0,0']['nodes']:
        fail('detour G(1,0,0) changed')
    job = min(jobs, key=lambda j: j['seconds'])
    args = ['--abc', '5,9,3', '--max-labellings', '100', '--pstar', str(job['pstars'][0])]
    for x in job['splits']:
        args += ['--split', '%d:%d:%d' % tuple(x)]
    r = run(args)
    if r['result'] != 'no labelling' or sum(x['nodes'] for x in r['pstars']) != job['nodes']:
        fail('detour chain-9 job %s changed' % job['file'])
    val = Path(tmp) / 'val'
    val.mkdir()
    res = subprocess.run([sys.executable, str(chk), 'validate', '--max-n', '12', '--max-steps', '5',
                          '--scratch', str(val), '--binary', binary], capture_output=True, text=True, check=True)
    v = json.loads(res.stdout[res.stdout.index('{'):])
    if v['mismatches'] != 0 or v['graphs_with_labellings'] == 0:
        fail('detour brute-force comparison failed')
    return {'critical_paths': len(seen), 'jobs': len(jobs), 'nodes': comb['total_nodes'],
            'g100_nodes': g['total_nodes'], 'replayed_job': job['file'],
            'brute_force_graphs': v['graphs'], 'brute_force_labellings': v['labellings_total']}


def recorded_source(rel, digest):
    """The committed version of `rel` whose sha256 is `digest` (the source a
    report was made with; the current file if it still matches)."""
    cur = exp.ROOT / rel
    if hashlib.sha256(cur.read_bytes()).hexdigest() == digest:
        return cur.read_bytes()
    revs = subprocess.run(['git', '-C', str(exp.ROOT), 'log', '--format=%H', '--', rel],
                          capture_output=True, text=True, check=True).stdout.split()
    for h in revs:
        data = subprocess.run(['git', '-C', str(exp.ROOT), 'show', '%s:%s' % (h, rel)],
                              capture_output=True, check=True).stdout
        if hashlib.sha256(data).hexdigest() == digest:
            return data
    fail('no committed version of %s has the recorded hash' % rel)


def check_chains(path, binary, tmp, rng):
    """Saved evidence for chains 1-8 and 10-16, rerun with the search source
    recorded in the report (taken from the git history if it has changed since)."""
    import experiment_clift5784689_chains as ch
    rep = json.loads(Path(path).read_text())
    rel = 'scripts/clift5784689_loss_search.cpp'
    data = recorded_source(rel, rep['input_sha256'][rel])
    if data != (exp.ROOT / rel).read_bytes():
        src = Path(tmp) / 'recorded_loss_search.cpp'
        src.write_bytes(data)
        binary = str(Path(tmp) / 'recorded_loss_search')
        subprocess.run(['c++'] + exp.FLAGS + ['-o', binary, str(src)], check=True)
    settled = {}
    for key, run in rep['chain_runs'].items():
        nodes, configs, runs = tree_totals(run)
        if nodes != run['nodes'] or runs != run['job_runs'] or configs or run['configurations']:
            fail('chain run %s totals inconsistent' % key)
        k = run['chain']
        a, b, c, s, var = ch.chain_params(k)
        extra = run.get('options', ch.opts(var, s))
        o = Path(tmp) / ('root_%d_%s.txt' % (k, run['anchor']))
        subprocess.run([binary, str(a), str(b), str(c), run['anchor'], str(o), 'split=10'] + extra,
                       capture_output=True, check=True)
        lines = [l for l in o.read_text().splitlines() if l.startswith('J')]
        if hashlib.sha256(''.join(l + '\n' for l in lines).encode()).hexdigest() != run['root_jobs_sha256']:
            fail('chain %d %s root jobs differ' % (k, run['anchor']))
        for rid, n in rng.sample(run['replay_sample'], min(2, len(run['replay_sample']))):
            r = subprocess.run([binary, str(a), str(b), str(c), 'resume', str(Path(tmp) / 'cr.txt')] + extra,
                               input=lines[int(rid.split('.')[1])] + '\n', capture_output=True, text=True, check=True)
            (Path(tmp) / 'cr.txt').unlink()
            got = json.loads(r.stdout.splitlines()[0])
            if got['nodes'] != n or got['configurations']:
                fail('chain %d job %s changed' % (k, rid))
        settled.setdefault(k, []).append(run['anchor'])
    for k in rep['chain_list']:
        a, b, c, s, var = ch.chain_params(k)
        if sorted(settled.get(k, [])) != sorted(['t'] + ([] if var[0] else ['A1'])):
            fail('chain %d: anchors missing' % k)
        d = rep['detour_runs'][str(k)]
        if d['result'] != 'no labelling' or len({j['pstar'] for j in d['jobs']}) != d['critical_paths']:
            fail('chain %d: detour coverage' % k)
    if sorted(settled) != sorted(rep['chain_list']):
        fail('chain runs do not match the chain list')
    caps = ch.chain_graph_tests(binary, rng, 40)
    return {'chains_settled': sorted(settled), 'chain_runs_checked': len(rep['chain_runs']),
            'caps_queries_per_chain_graph': 40, 'chain_graph_caps_tests': len(caps)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('report', type=Path)
    ap.add_argument('--samples', type=int, default=24)
    ap.add_argument('--detour', type=Path, default=None)
    ap.add_argument('--chains', type=Path, default=None)
    ap.add_argument('--only-chains', action='store_true',
                    help='check only the --chains report (the first argument is then ignored)')
    args = ap.parse_args()
    if args.only_chains:
        out = {}
        with tempfile.TemporaryDirectory() as tmp:
            binary, version = exp.compile_search(tmp)
            out['compiler'] = version
            out['chains'] = check_chains(args.chains, binary, tmp, random.Random(20261020))
        out['status'] = 'checked'
        print(json.dumps(out))
        return
    rep = json.loads(args.report.read_text())
    out = {}
    # structure
    for name, case in rep['reference_comparison'].items():
        if case['cost_n_minus_1_labellings'] != 0:
            fail('reference case %s has a labelling' % name)
    for name, case in rep['ladder'].items():
        if case['configurations'] != 0:
            fail('ladder case %s not excluded' % name)
    if not any(r['search_found'] for r in rep['positive_control']):
        fail('positive control never positive')
    if any(r['search_found'] != r['leaf_accepted'] for r in rep['positive_control']):
        fail('positive control mismatch')
    totals = {}
    for anchor in ('t', 'A1'):
        c9 = rep['chain9'][anchor]
        nodes, configs, runs = tree_totals(c9)
        if nodes != c9['nodes'] or runs != c9['job_runs'] or configs != 0 or c9['configurations']:
            fail('chain-9 %s totals inconsistent' % anchor)
        totals[anchor] = nodes
    out['chain9_nodes'] = totals
    with tempfile.TemporaryDirectory() as tmp:
        binary, version = exp.compile_search(tmp)
        out['compiler'] = version
        # G(1,0,0): C++ without caps equals the reference; every leaf excluded
        total = 0
        for anchor in ('t', 'A1'):
            R = ref.Reference(1, 0, 0, anchor)
            py = sorted(exp.key((a, sorted(d))) for a, d in R.run())
            _, cfgs = exp.run_cpp(binary, 1, 0, 0, anchor, Path(tmp) / 'x.txt', ['nolp'])
            if py != sorted(exp.key(c) for c in cfgs):
                fail('reference differs at 109 %s' % anchor)
            total += len(py)
            for cfg in cfgs:
                chk = ref.budget_check(1, 0, 0, *cfg)
                if not chk['interval'] or chk['feasible']:
                    fail('109 configuration check failed')
            stats, cfgs = exp.run_cpp(binary, 1, 0, 0, anchor, Path(tmp) / 'y.txt')
            if cfgs or stats['nodes'] != rep['ladder']['1,0,0,%s' % anchor]['nodes']:
                fail('109 pruned search changed')
        if total != 48:
            fail('G(1,0,0) configuration count changed')
        out['g100_reference_configurations'] = total
        rng = random.Random(rep['seed'] + 1)
        out['caps_soundness'] = exp.decomposition_and_lp_tests(binary, rng, 200)
        # chain-9 root splits and a sample of small root jobs
        sampled = []
        for anchor in ('t', 'A1'):
            c9 = rep['chain9'][anchor]
            o = Path(tmp) / ('root_%s.txt' % anchor)
            subprocess.run([binary, '5', '9', '3', anchor, str(o), 'split=10'], capture_output=True, check=True)
            lines = [l for l in o.read_text().splitlines() if l.startswith('J')]
            digest = hashlib.sha256(''.join(l + '\n' for l in lines).encode()).hexdigest()
            if digest != c9['root_jobs_sha256']:
                fail('chain-9 %s root jobs differ' % anchor)
            pick = rng.sample(c9['replay_sample'], min(args.samples // 2, len(c9['replay_sample'])))
            for rid, nodes in pick:
                line = lines[int(rid.split('.')[1])]
                res = subprocess.run([binary, '5', '9', '3', 'resume', str(Path(tmp) / 'r.txt')],
                                     input=line + '\n', capture_output=True, text=True, check=True)
                (Path(tmp) / 'r.txt').unlink()
                got = json.loads(res.stdout.splitlines()[0])
                if got['nodes'] != nodes or got['configurations']:
                    fail('chain-9 job %s %s changed' % (anchor, rid))
                sampled.append([anchor, rid, nodes])
        out['chain9_jobs_replayed'] = len(sampled)
        if args.detour:
            out['detour'] = check_detour(args.detour, tmp)
        if args.chains:
            out['chains'] = check_chains(args.chains, binary, tmp, rng)
    out['status'] = 'checked'
    print(json.dumps(out))


if __name__ == '__main__':
    main()
