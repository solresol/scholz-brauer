#!/usr/bin/env python3
"""Bounded complete position scans at saved fixed box roles.

This does not enumerate outer boxes. Compare the signed-fingerprint pruning
with all structurally valid exception placements, retaining prescribed halves
through the existing full-shape classifier. Lean proves position coverage.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from itertools import combinations
import json
from pathlib import Path
import platform
import signal
import subprocess
import time

from experiment_clift109_common_box import compatibility_gap
from experiment_clift109_sink_classifier import classify

ROOT = Path(__file__).resolve().parents[1]
SAVED = ROOT / 'results/2026-10-18-clift109-box-exclusion.json'


def scan(box):
    box = list(box[:7]) + [0]*5
    u, v, w, d, d2, d3, t = box[:7]
    points = [t + sum(xs) for n in range(7)
              for xs in combinations((u, v, w, d, d2, d3), n)]
    if len(set(points)) != 64 or not set(points) <= set(range(109)):
        raise ValueError('scan requires an interval dissociated box')
    rest = set(range(109)) - set(points)
    digit = lambda x: (-1 if x // d % 2 else 1) * 4**(x % d)
    target = sum(digit(x) for x in range(109))
    residue_counts = Counter(x % d for x in range(109))
    odd_residues = {r for r, n in residue_counts.items() if n % 2}
    counts = Counter()
    choices, accepted, unpruned = [], [], []
    for r in sorted(rest):
        rectangle = [r, r+u, r+v, r+u+v]
        if len(set(rectangle)) != 4 or not set(rectangle) <= rest:
            continue
        counts['rectangles'] += 1
        if len(odd_residues) != 7 or r % d in odd_residues:
            counts['residue_allowed_rectangles'] += 1
        after_rectangle = rest - set(rectangle)
        for s in sorted(after_rectangle):
            pair = [s, s+u]
            if len(set(pair)) != 2 or not set(pair) <= after_rectangle:
                continue
            counts['rectangle_pair_choices'] += 1
            for z in sorted(after_rectangle-set(pair)):
                counts['unpruned_positions'] += 1
                # Independently check the exact seven-point structural condition.
                if Counter(rectangle+pair+[z]) - Counter(rest):
                    raise ValueError('staged subtraction lost multiplicities')
                tuples = classify(box, r, s, z)
                unpruned.extend(tuples)
                allowed = len(odd_residues) != 7 or all(
                    x % d in odd_residues for x in (r, s, z))
                if allowed and sum(map(digit, rectangle+pair+[z])) == target:
                    choices.append([r, s, z])
                    accepted.extend(tuples)
                elif tuples:
                    raise ValueError('fingerprint removed an interval tuple')
    if sorted(accepted) != sorted(unpruned):
        raise ValueError('pruned and unpruned position scans differ')
    return {'box_roles': list(box[:7]), 'counts': dict(counts),
            'fingerprint_position_choice_count': len(choices),
            'fingerprint_positions_sha256': hashlib.sha256(
                json.dumps(choices, separators=(',', ':')).encode()).hexdigest(),
            **({'fingerprint_position_choices': choices}
               if box[:7] == [1, 2, 4, 51, 23, 8, 0] else {}),
            'accepted_coordinates': sorted(accepted),
            'accepted_position_anchor_records': sorted(
                [c[9]+c[7], c[10]+c[7], c[11]+c[7], c[11]] for c in accepted)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('refusing to replace existing evidence')
    signal.alarm(120)
    tic = time.monotonic()
    saved = json.loads(SAVED.read_text())['configurations']
    boxes = sorted({tuple(c[:7]) for c in saved})
    if len(boxes) != 48 or len(saved) != 216:
        raise ValueError('unexpected saved fixture scope')
    rows = []
    for box in boxes:
        row = scan(box)
        expected = sorted(c for c in saved if tuple(c[:7]) == box)
        if row['accepted_coordinates'] != expected:
            raise ValueError('new/missing completion at saved box roles')
        rows.append(row)
    gap = scan(compatibility_gap()['coordinates'])
    if gap['accepted_coordinates']:
        raise ValueError('relaxed box unexpectedly has an interval completion')
    files = [Path(__file__), SAVED, ROOT/'scripts/experiment_clift109_sink_classifier.py',
             ROOT/'scripts/experiment_clift109_common_box.py',
             ROOT/'scripts/experiment_clift109_half_reconstruction.py',
             ROOT/'scripts/experiment_clift109_box.py', ROOT/'scripts/clift109_box_dual.py',
             ROOT/'lean/ScholzBrauer/Clift109SinkPositions.lean',
             ROOT/'lean/ScholzBrauer/Clift109SinkPositionChecks.lean',
             ROOT/'lean/ScholzBrauer/Clift109SinkPositionCaps.lean',
             *sorted((ROOT/'lean/ScholzBrauer').glob('Clift109SinkPositionCapChecks*.lean'))]
    report = {'accessed_at_utc': datetime.now(timezone.utc).isoformat(),
              'base_commit': subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
              'command': ['python3','scripts/experiment_clift109_sink_positions.py','--output',str(args.output)],
              'python':platform.python_version(),'dependencies':'Python standard library and existing project modules',
              'random_seed':None,'timeout_seconds':120,'elapsed_seconds':time.monotonic()-tic,
              'bounds':{'interval':[0,108],'fixed_saved_box_roles':48,'relaxed_gap_box_roles':1,
                        'position_domain':'Every disjoint rectangle/pair/singleton in the 45-point box complement'},
              'saved_interval_completions':sum(len(r['accepted_coordinates']) for r in rows),
              'unpruned_position_choices':sum(r['counts']['unpruned_positions'] for r in rows+[gap]),
              'fixed_box_scans':rows,'relaxed_gap_box_scan':gap,
              'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
              'claim_boundary':'Complete finite position scans ONLY at the listed 49 fixed box roles. '
                               'No complete outer-box enumeration, pair removal, cap feasibility, '
                               'kernel proof of every scan, full 108 exclusion or new Scholz instance. '
                               'Both scans share the existing full-shape classifier; their position pruning differs.'}
    with args.output.open('x') as f:
        json.dump(report,f,indent=2); f.write('\n')
    print(json.dumps({k:report[k] for k in ('saved_interval_completions','unpruned_position_choices','elapsed_seconds')}))


if __name__=='__main__':
    main()
