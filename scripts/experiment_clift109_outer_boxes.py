#!/usr/bin/env python3
"""Bound and cross-check the newly proved outer box domain, without graph search.

The suffix recurrence follows dissociatedDimensions' exact specification.
Compare its ENTIRE output with the existing independent prefix bit-popcount
generator. Count roles/translations and check saved fixtures for membership;
fixture completeness, interval completion and caps are not inferred.
"""
import argparse
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import platform
import signal
import subprocess
import time

from clift109_box_dual import distinct_subset_sum_sets

ROOT = Path(__file__).resolve().parents[1]


@lru_cache(None)
def dimensions(n, lower, budget):
    """Enumerate sorted suffixes; a bit collision rejects repeated subset sums."""
    if not n:
        return (((), 1),)
    out = []
    for d in range(lower, budget // n + 1):
        for ds, support in dimensions(n - 1, d, budget - d):
            if not support & (support << d):
                out.append(((d,) + ds, support | (support << d)))
    return tuple(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('refusing to replace existing evidence')
    signal.alarm(90)
    started = time.monotonic()
    stamp = datetime.now(timezone.utc).isoformat()
    t = time.monotonic()
    suffix = dimensions(6, 1, 108)
    sets = [ds for ds, _ in suffix]
    suffix_seconds = time.monotonic() - t
    if len(sets) != len(set(sets)) or sets != sorted(sets):
        raise ValueError('duplicate or unsorted generated dimensions')
    for ds, support in suffix:
        # Independent explicit construction checks multiplicity in every box.
        weights = [sum(d for i, d in enumerate(ds) if mask >> i & 1)
                   for mask in range(64)]
        if len(set(weights)) != 64 or sum(1 << x for x in weights) != support:
            raise ValueError('incorrect subset-sum support')
    t = time.monotonic()
    prefix = sorted(distinct_subset_sum_sets())
    prefix_seconds = time.monotonic() - t
    if sets != prefix:
        raise ValueError('complete prefix and suffix domains disagree')
    offsets = sum(109 - sum(ds) for ds in sets)
    if [len(sets), offsets] != [31048, 263256]:
        raise ValueError('unexpected outer domain: inspect before publication')
    pairs_path = ROOT / 'results/2026-11-09-placed-pairs.json'
    pairs = set(map(tuple, json.loads(pairs_path.read_text())['surviving_pairs']))
    if len(pairs) != 278:
        raise ValueError('unexpected checked pair-domain fixture')
    packing = {pair: 0 for pair in pairs}
    for ds in sets:
        translations = 109 - sum(ds)
        for u in ds:
            for d in ds:
                if (u, d) in packing:
                    packing[u, d] += translations
    common_path = ROOT / 'results/2026-11-13-common-box.json'
    common = json.loads(common_path.read_text())
    if packing != {tuple(r['pair']): r['packing_boxes'] for r in common['counts']}:
        raise ValueError('packing projection differs from independently saved counts')
    saved_path = ROOT / 'results/2026-10-18-clift109-box-exclusion.json'
    saved = json.loads(saved_path.read_text())['configurations']
    domain = set(sets)
    role_inputs = set()
    for c in saved:
        u, v, w, d1, d2, d3, t = c[:7]
        ds = sorted((u, v, w, d1, d2, d3))
        if tuple(ds) not in domain or not 0 <= t < 109 - sum(ds):
            raise ValueError('saved fixture outside complete outer domain')
        if (u, d1) not in pairs:
            raise ValueError('saved fixture outside checked step domain')
        role_inputs.add(tuple(c[:7]))
    files = [Path(__file__), ROOT / 'scripts/clift109_box_dual.py', pairs_path,
             common_path, saved_path, ROOT / 'lean/ScholzBrauer/Clift109OuterBoxes.lean']
    report = {
        'started_at_utc': stamp,
        'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'command': ['python3', 'scripts/experiment_clift109_outer_boxes.py', '--output', str(args.output)],
        'python': platform.python_version(), 'random_seed': None,
        'dependencies': 'Python standard library and existing project module',
        'timeout_seconds': 90,
        'bounds': {'dimensions': 6, 'minimum_dimension': 1, 'dimension_sum_max': 108,
                   'translation': '0 <= t <= 108 - sum(dimensions)',
                   'ordered_step_pairs': 278},
        'dimension_sets': len(sets), 'dimension_set_offsets': offsets,
        'dimension_sets_sha256': hashlib.sha256(
            json.dumps(sets, separators=(',', ':')).encode()).hexdigest(),
        'complete_prefix_suffix_equality': True,
        'every_subset_sum_support_independently_replayed': True,
        'unpruned_ordered_role_inputs': 720 * offsets,
        'checked_pair_ordered_role_inputs': 24 * sum(packing.values()),
        'saved_common_box_projections': {
            'both_odd_run_ordered_role_inputs': 24 * sum(r['both_odd_run_boxes'] for r in common['counts']),
            'top_pinned_ordered_role_inputs': 24 * sum(r['top_pinned_boxes'] for r in common['counts']),
            'scope': 'Derived from saved independent exact common-box counts; odd-run counts not rerun here.'},
        'saved_fixture_membership': {'coordinate_tuples': len(saved), 'ordered_role_inputs': len(role_inputs)},
        'timings': {'suffix_seconds': suffix_seconds, 'prefix_seconds': prefix_seconds},
        'elapsed_seconds': time.monotonic() - started,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'claim_boundary': 'Lean separately proves exact generator specification and complete outer-role coverage. '
                          'These cardinalities and the prefix/suffix equality are computational. '
                          'No full kernel cardinality, outer interval-output classification, new cap exclusion, '
                          'pair removal, full 108 exclusion or new Scholz instance.'}
    with args.output.open('x') as f:
        json.dump(report, f, indent=2)
        f.write('\n')
    print(json.dumps({k: report[k] for k in ('dimension_sets', 'dimension_set_offsets',
          'unpruned_ordered_role_inputs', 'checked_pair_ordered_role_inputs', 'elapsed_seconds')}))


if __name__ == '__main__':
    main()
