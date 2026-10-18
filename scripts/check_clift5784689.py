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

It does not repeat the multi-hour search; completeness is the experiment's
claim. Standard library only.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess
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


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('report', type=Path)
    ap.add_argument('--samples', type=int, default=24)
    args = ap.parse_args()
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
    out['status'] = 'checked'
    print(json.dumps(out))


if __name__ == '__main__':
    main()
