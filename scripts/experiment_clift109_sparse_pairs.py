"""Exhaust the interval classifier for the sparsest nonempty common-box pairs."""
import argparse
from collections import Counter
import json
from pathlib import Path
import platform
import time

from experiment_clift109_gap_slice import classify_slice
from experiment_clift109_outer_boxes import dimensions


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-boxes", type=int, default=1)
    parser.add_argument("--max-boxes", type=int, default=8)
    args = parser.parse_args()
    if not 1 <= args.min_boxes <= args.max_boxes:
        parser.error("require 1 <= min-boxes <= max-boxes")
    started = time.monotonic()
    root = Path(__file__).resolve().parents[1]
    rows = json.loads((root / 'results/2026-11-13-common-box.json').read_text())['counts']
    boxes = dimensions(6, 1, 108)
    results = []
    for row in rows:
        if not args.min_boxes <= row['both_odd_run_boxes'] <= args.max_boxes:
            continue
        u, d = row['pair']
        counts = Counter(halvable_triples_before_role_expansion=0)
        solutions = []
        for ds, _ in boxes:
            if u in ds and d in ds:
                free = tuple(k for k in ds if k not in (u, d))
                part = classify_slice(u, d, free)
                counts.update(part['counts'])
                solutions.extend(part['solutions'])
        if (counts['role_inputs'] != 24 * row['packing_boxes'] or
                counts['odd_run_surviving_inputs'] != 24 * row['both_odd_run_boxes']):
            raise ValueError(f'common-box projection mismatch for {(u, d)}')
        results.append(dict(pair=[u, d], counts=counts, solutions=solutions))
    print(json.dumps(dict(rows=results, python=platform.python_version(),
                          seconds=time.monotonic()-started), indent=2))


if __name__ == '__main__':
    main()
