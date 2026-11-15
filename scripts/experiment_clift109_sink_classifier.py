#!/usr/bin/env python3
"""Check the fixed-box/actual-position classifier, without outer enumeration.

Replay all saved interval fixtures. Compare three fixed inputs with an
independent direct enumeration of bounded anchor/q coordinates, and reject
the earlier relaxed common-box example. Lean proves the general classifier
separately; these finite checks do not certify outer enumeration or caps.
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

from clift109_box_dual import halve
from experiment_clift109_box import decomposition
from experiment_clift109_common_box import compatibility_gap
from experiment_clift109_half_reconstruction import reconstruct, sink_half

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'results/2026-10-18-clift109-box-exclusion.json'
INTERVAL = list(range(109))


def classify(box, r, s, z):
    u, v, w, d1, d2, d3, t, *_ = box
    points = [t + sum(xs) for n in range(7)
              for xs in combinations((u, v, w, d1, d2, d3), n)]
    exceptions = [r, r+u, r+v, r+u+v, s, s+u, z]
    # This fast path requires a genuine partition, never truncated subtraction.
    occupied = Counter(points + exceptions)
    if any(x < 0 or x > 108 or count != 1 for x, count in occupied.items()):
        return []
    remainder = sum(1 << x for x in INTERVAL if x not in occupied)
    half = halve(remainder, d1)
    if half is None:
        return []
    h = [x for x in INTERVAL if half >> x & 1]
    if sorted(points + h + [x+d1 for x in h] + exceptions) != INTERVAL:
        raise ValueError('halving did not recover a full partition')
    out = []
    for anchor in h:
        c = reconstruct(box, h, r, s, z, anchor)
        if sorted(sink_half(c)) == h:
            if decomposition(c) != INTERVAL:
                raise ValueError('accepted shape did not solve the interval')
            out.append(c)
    if len(out) > 2:
        raise ValueError('at-most-two bound violated')
    return sorted(out)


def direct(box, r, s, z):
    """No halving or moment recovery: enumerate bounded anchor and q directly.

    In an interval tuple A3 and A3+q belong to its prescribed sink half,
    hence 0<=A3<=108 and -108<=q<=108. The full 109-weight equation decides.
    This is a bounded computational comparison, not a Lean coverage proof.
    """
    out = []
    for anchor in INTERVAL:
        for q in range(-108, 109):
            c = list(box[:7]) + [z-anchor, q, r-z+anchor, s-z+anchor, anchor]
            if decomposition(c) == INTERVAL:
                out.append(c)
    return sorted(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('refusing to replace an existing report')
    signal.alarm(60)
    started = time.monotonic()
    fixtures = json.loads(INPUT.read_text())['configurations']
    if len(fixtures) != 216:
        raise ValueError('unexpected fixture input')
    rows = []
    controls = 0
    for i, c in enumerate(fixtures):
        r, s, z = (c[j] + c[7] for j in (9, 10, 11))
        accepted = classify(c, r, s, z)
        if c not in accepted or len(accepted) != 1:
            raise ValueError('saved interval tuple lost or changed local count')
        # Out-of-interval singleton, excessive box, and duplicate exceptions.
        bad_box = list(c)
        bad_box[6] += 109
        for prototype, positions in ((c, (r, s, 109)),
                                     (bad_box, (r, s, z)), (c, (r, r, z))):
            if classify(prototype, *positions):
                raise ValueError('invalid partition accepted')
            controls += 1
        rows.append({'fixture_index': i, 'anchors': [x[11] for x in accepted]})
    gap = compatibility_gap()['coordinates']
    cases = [(fixtures[0], (104, 102, 108)), (gap, (66, 69, 1)),
             (fixtures[0], (104, 102, 109))]
    comparisons = []
    for box, positions in cases:
        fast = classify(box, *positions)
        brute = direct(box, *positions)
        if fast != brute:
            raise ValueError('direct anchor/q enumeration disagrees')
        comparisons.append({'box_roles': box[:7], 'positions': positions,
                            'direct_coordinate_pairs_checked': 109*217,
                            'accepted_coordinates': fast})
    if comparisons[1]['accepted_coordinates']:
        raise ValueError('relaxed gap unexpectedly has an interval completion')
    paths = [Path(__file__), INPUT,
             *(ROOT/'scripts'/name for name in ('clift109_box_dual.py',
               'experiment_clift109_box.py', 'experiment_clift109_common_box.py',
               'experiment_clift109_half_reconstruction.py')),
             *(ROOT/'lean/ScholzBrauer'/name for name in
               ('Clift109SinkClassifier.lean', 'Clift109SinkClassifierChecks.lean'))]
    report = {
        'accessed_at_utc': datetime.now(timezone.utc).isoformat(),
        'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                                              cwd=ROOT, text=True).strip(),
        'command': ['python3', 'scripts/experiment_clift109_sink_classifier.py',
                    '--output', str(args.output)],
        'python': platform.python_version(), 'random_seed': None,
        'dependencies': 'Python standard library and existing project modules',
        'timeout_seconds': 60, 'elapsed_seconds': time.monotonic()-started,
        'bounds': {'interval': [0, 108], 'saved_fixtures': 216,
                   'direct_anchor': [0, 108], 'direct_q': [-108, 108],
                   'direct_fixed_inputs': 3},
        'saved_configurations_recovered': len(rows), 'corruptions_rejected': controls,
        'fixtures': rows, 'independent_direct_comparisons': comparisons,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in paths},
        'claim_boundary': 'Fixed-input classifier checks only; the local iff and '
                          'at-most-two bound are proved separately in Lean. No outer '
                          'enumeration completeness, pair removal, cap feasibility, '
                          'full 108-doubling exclusion or new Scholz instance follows.'}
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k: report[k] for k in ('saved_configurations_recovered',
                      'corruptions_rejected', 'elapsed_seconds')}))


if __name__ == '__main__':
    main()
