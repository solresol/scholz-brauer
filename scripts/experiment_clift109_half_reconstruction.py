#!/usr/bin/env python3
"""Check moment reconstruction on saved interval fixtures, without enumeration.

Compare a direct scan of the nineteen recovered half-weights with integer
quadratic roots. This does not certify completeness of the saved 216 fixtures,
the common-box refinement, cap feasibility, or the selected-109 exclusion.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
from itertools import combinations
import json
from math import isqrt
from pathlib import Path
import platform
import signal
import subprocess
import time

from clift109_box_dual import halve
from experiment_clift109_box import decomposition

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'results/2026-10-18-clift109-box-exclusion.json'


def sink_half(c):
    u, v, _, _, d2, _, _, _, q, a1, a2, a3 = c
    return ([a1 + x + y for x in (0, u, v, u + v) for y in (0, d2, q)]
            + [a2 + x + y for x in (0, u) for y in (0, d2)]
            + [a3 + y for y in (0, d2, q)])


def reconstruct(c, h, r, s, z, anchor):
    out = list(c)
    u, v, d2 = c[0], c[1], c[4]
    out[7] = z - anchor
    out[8] = (sum(h) - 12*r - 4*s + 16*z - 19*anchor - 8*u - 6*v - 7*d2) // 5
    out[9:] = [r - z + anchor, s - z + anchor, anchor]
    return out


def moments(h):
    return sum(h), sum(x*x for x in h)


def quadratic_anchors(c, h, r, s, z):
    """Solve the two-translation moment equations, without scanning h."""
    u, v, d2 = c[0], c[1], c[4]
    k = ([r-z+x+y for x in (0, u, v, u+v) for y in (0, d2)]
         + [s-z+x+y for x in (0, u) for y in (0, d2)] + [0, d2])
    p = [r-z+x for x in (0, u, v, u+v)] + [0]
    assert len(k) == 14 and len(p) == 5
    C = sum(h) - sum(k) - sum(p)
    D = moments(h)[1] - moments(k)[1] - moments(p)[1]
    linear = 10*sum(k) - 28*sum(p) - 28*C
    constant = C*C + 2*sum(p)*C - 5*D
    discriminant = linear*linear - 4*266*constant
    if discriminant < 0:
        return []
    root = isqrt(discriminant)
    if root*root != discriminant:
        return []
    candidates = set()
    for numerator in (-linear-root, -linear+root):
        if numerator % 532 == 0:
            anchor = numerator // 532
            if anchor in h and (C-14*anchor) % 5 == 0:
                candidates.add(anchor)
    return sorted(candidates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('refusing to replace an existing report')
    signal.alarm(60)
    started = time.monotonic()
    fixtures = json.loads(INPUT.read_text())['configurations']
    assert len(fixtures) == 216
    rows, distribution = [], Counter()
    for index, c in enumerate(fixtures):
        assert decomposition(c) == list(range(109))
        u, v, w, d1, d2, d3, t, p, _, a1, a2, a3 = c
        box = {t+sum(xs) for n in range(7)
               for xs in combinations((u, v, w, d1, d2, d3), n)}
        r, s, z = a1+p, a2+p, a3+p
        exceptions = {r, r+u, r+v, r+u+v, s, s+u, z}
        assert len(box) == 64 and len(exceptions) == 7 and not box & exceptions
        mask = sum(1 << x for x in set(range(109)) - box - exceptions)
        half_mask = halve(mask, d1)
        assert half_mask is not None
        h = [x for x in range(109) if half_mask >> x & 1]
        assert len(h) == 19 and sorted(sink_half(c)) == h and a3 in h
        assert reconstruct(c, h, r, s, z, a3) == c
        scanned = [a for a in h if moments(sink_half(reconstruct(c, h, r, s, z, a))) == moments(h)]
        roots = quadratic_anchors(c, h, r, s, z)
        assert scanned == roots and a3 in roots and len(roots) <= 2
        exact = [a for a in roots if sorted(sink_half(reconstruct(c, h, r, s, z, a))) == h]
        assert a3 in exact
        # A q corruption changes the first moment; a balanced endpoint
        # corruption preserves the first moment but changes the second.
        bad_q = list(c)
        bad_q[8] += 1
        assert moments(sink_half(bad_q))[0] != moments(h)[0]
        bad_half = list(h)
        bad_half[0] -= 1
        bad_half[-1] += 1
        assert sum(bad_half) == sum(h) and moments(bad_half)[1] != moments(h)[1]
        distribution[len(roots)] += 1
        rows.append({'fixture_index': index, 'anchor': a3,
                     'moment_anchors': roots, 'exact_shape_anchors': exact})
    paths = [Path(__file__), INPUT, ROOT/'scripts/clift109_box_dual.py',
             ROOT/'scripts/experiment_clift109_box.py',
             ROOT/'lean/ScholzBrauer/Clift109HalfReconstruction.lean']
    report = {
        'accessed_at_utc': datetime.now(timezone.utc).isoformat(),
        'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'python': platform.python_version(), 'random_seed': None,
        'dependencies': 'Python standard library and existing project modules',
        'command': ['python3', 'scripts/experiment_clift109_half_reconstruction.py', '--output', str(args.output)],
        'timeout_seconds': 60, 'elapsed_seconds': time.monotonic()-started,
        'bounds': {'interval': [0, 108], 'saved_fixtures': 216, 'anchors_scanned_each': 19},
        'moment_anchor_count_distribution': dict(sorted(distribution.items())),
        'independent_quadratic_agreement': True,
        'actual_coordinates_recovered': len(rows), 'corruptions_detected': 2*len(rows),
        'fixtures': rows,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'claim_boundary': 'Fixture checks and independent exact moment calculations only. '
                          'The at-most-two bound is proved separately in Lean for arbitrary integer multisets. '
                          'No enumeration completeness, pair refinement, cap feasibility or full exclusion follows.'}
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k: report[k] for k in ('actual_coordinates_recovered',
          'moment_anchor_count_distribution', 'corruptions_detected', 'elapsed_seconds')}))


if __name__ == '__main__':
    main()
