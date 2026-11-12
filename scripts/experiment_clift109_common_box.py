#!/usr/bin/env python3
"""Bound the next common-box reduction and exhibit its compatibility gap.

Two complete box enumerations count the 278 input pairs satisfying BOTH
odd-run bounds on one common box. This does not repeat the completed graph
enumeration or prove a finite reduction in Lean. An explicit coordinate tuple
additionally passes both actual-exception placements with unrelated halves;
the exact witness is independently replayed here and kernel checked separately.
"""
import argparse
from datetime import datetime, timezone
import hashlib
from itertools import combinations
import json
from pathlib import Path
import platform
import signal
import subprocess
import tempfile
import time

import clift109_box_dual as dual
from experiment_clift109_box import decomposition

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'results/2026-11-09-placed-pairs.json'
SAVED = ROOT / 'results/2026-10-18-clift109-box-exclusion.json'
CPP = ROOT / 'scripts/clift109_common_box.cpp'


def odd_runs(support, step):
    """Count maximal arithmetic runs directly, without pair peeling."""
    count = 0
    for x in support:
        if x - step in support:
            continue
        length = 1
        while x + length * step in support:
            length += 1
        count += length % 2
    return count


def python_counts(pairs):
    counts = {p: [0, 0, 0] for p in pairs}
    sets = dual.distinct_subset_sum_sets()
    offsets = 0
    for xs in sets:
        sums = {sum(c) for n in range(7) for c in combinations(xs, n)}
        if len(sums) != 64:
            raise ValueError('box generator accepted repeated subset sums')
        roles = [(m, d) for m in xs for d in xs if (m, d) in counts]
        for t in range(109 - sum(xs)):
            offsets += 1
            support = set(range(109)) - {x + t for x in sums}
            good = {m: odd_runs(support, m) <= 7 for m in xs}
            for pair in roles:
                row = counts[pair]
                row[0] += 1
                if all(good[m] for m in pair):
                    row[1] += 1
                    row[2] += t + sum(xs) == 108
    return counts, [len(sets), offsets]


def replay_placement(box, half, regular, opposite, starts, singleton):
    """Explicit list construction checks all multiplicities and every point."""
    values = list(box) + list(half) + [x + regular for x in half]
    values += [x for start in starts for x in (start, start + opposite)]
    values += [singleton]
    if len(box) != 64 or len(half) != 19 or sorted(values) != list(range(109)):
        raise ValueError('common-box placement does not partition [0,108]')


def compatibility_gap():
    # One tuple fixes BOTH actual exception multisets, not only their singleton.
    # Order: u,v,w,d1,d2,d3,t,p,q,A1,A2,A3.
    cfg = [2, 16, 8, 3, 4, 32, 0, -63, 2, 129, 132, 64]
    u, v, w, d1, d2, d3, t, p, q, A1, A2, A3 = cfg
    box = [t + sum(c) for n in range(7)
           for c in combinations((u, v, w, d1, d2, d3), n)]
    source = [70, 73, 74, 77, 78, 81, 82, 85, 86, 89, 90, 93, 94, 97, 98, 101, 102, 105, 106]
    sink = [64, 70, 72, 74, 76, 78, 80, 85, 86, 87, 91, 92, 93, 97, 98, 99, 103, 104, 105]
    source_starts = [A3, A3 + d2, A3 + q]
    sink_starts = [A1 + p, A1 + p + v, A2 + p]
    singleton = A3 + p
    replay_placement(box, source, u, d1, source_starts, singleton)
    replay_placement(box, sink, d1, u, sink_starts, singleton)
    rejected = 0
    for half, regular, opposite, starts, point in (
            (source[:-1], u, d1, source_starts, singleton),
            (source, u, d1, [64, 64, 66], singleton),
            (sink, d1, u, sink_starts, 2)):
        try:
            replay_placement(box, half, regular, opposite, starts, point)
        except ValueError:
            rejected += 1
        else:
            raise ValueError('corrupt compatibility witness accepted')
    if decomposition(cfg) == list(range(109)):
        raise ValueError('gap tuple unexpectedly solves the whole interval')
    return {'coordinates': cfg, 'singleton': singleton,
            'source_starts': source_starts, 'sink_starts': sink_starts,
            'source_half': source, 'sink_half': sink,
            'common_box_span': sum((u, v, w, d1, d2, d3)),
            'whole_interval_equation': False,
            'corrupt_witnesses_rejected': rejected}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('refusing to replace an existing report')
    signal.alarm(180)
    started = time.monotonic()
    timestamp = datetime.now(timezone.utc).isoformat()
    pairs = list(map(tuple, json.loads(INPUT.read_text())['surviving_pairs']))
    if len(set(pairs)) != 278 or set(pairs) != {p[::-1] for p in pairs}:
        raise ValueError('unexpected input domain')
    timings = {}
    with tempfile.TemporaryDirectory(prefix='clift109-common-box-') as temp:
        binary = Path(temp) / 'common-box'
        compile_argv = ['g++', '-O3', '-std=c++17', '-Wall', '-Wextra', '-Werror',
                        str(CPP), '-o', str(binary)]
        subprocess.run(compile_argv, check=True, timeout=30)
        t = time.monotonic()
        proc = subprocess.run([str(binary)], check=True, text=True,
                              input=''.join(f'{m} {d}\n' for m, d in pairs),
                              stdout=subprocess.PIPE, timeout=60)
        timings['cpp_seconds'] = time.monotonic() - t
        lines = proc.stdout.splitlines()
        stats = list(map(int, lines[0].split()[1:]))
        cpp = {}
        for line in lines[1:]:
            tag, m, d, packing, odd, top = line.split()
            if tag != 'D' or (int(m), int(d)) in cpp:
                raise ValueError('invalid or duplicate C++ decision')
            cpp[int(m), int(d)] = list(map(int, (packing, odd, top)))
    t = time.monotonic()
    counts, py_stats = python_counts(pairs)
    timings['python_seconds'] = time.monotonic() - t
    if cpp != counts or stats != py_stats or stats != [31048, 263256]:
        raise ValueError('independent complete common-box counts disagree')
    retained = [p for p in pairs if counts[p][1]]
    rejected = [p for p in pairs if not counts[p][1]]
    top_retained = [p for p in pairs if counts[p][2]]
    if len(retained) != 246 or top_retained != retained or not all(counts[p][0] for p in pairs):
        raise ValueError('unexpected reduction; inspect before publishing')
    saved = json.loads(SAVED.read_text())['configurations']
    for cfg in saved:
        u, v, w, d1, d2, d3, t, *_ = cfg
        sums = {t + sum(c) for n in range(7)
                for c in combinations((u, v, w, d1, d2, d3), n)}
        support = set(range(109)) - sums
        if (u, d1) not in retained or any(odd_runs(support, m) > 7 for m in (u, d1)):
            raise ValueError('saved interval configuration lost')
    witness = compatibility_gap()
    paths = [Path(__file__), CPP, INPUT, SAVED,
             ROOT / 'scripts/clift109_box_search.cpp',
             ROOT / 'scripts/clift109_box_dual.py',
             ROOT / 'scripts/experiment_clift109_box.py',
             ROOT / 'lean/ScholzBrauer/Clift109CommonBoxExample.lean']
    report = {
        'started_at_utc': timestamp,
        'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'python': platform.python_version(),
        'compiler': subprocess.check_output(['g++', '--version'], text=True).splitlines()[0],
        'compile_argv': compile_argv, 'random_seed': None,
        'timeout_seconds': 180, 'cpp_timeout_seconds': 60,
        'dependencies': 'Python standard library and existing project modules; g++ C++17',
        'bounds': {'interval': [0, 108], 'box_dimensions': 6,
                   'distinct_subset_sum_sets': stats[0], 'set_offsets': stats[1],
                   'ordered_input_pairs': 278, 'odd_runs_each_step_at_most': 7},
        'retained_pair_count': len(retained), 'rejected_pairs': rejected,
        'retained_pairs': retained, 'top_pinned_retained_pairs': top_retained,
        'two_three_counts': counts[2, 3],
        'counts': [{'pair': p, 'packing_boxes': counts[p][0],
                    'both_odd_run_boxes': counts[p][1], 'top_pinned_boxes': counts[p][2]}
                   for p in pairs],
        'saved_configurations_preserved': len(saved),
        'compatibility_gap_witness': witness,
        'timings': timings, 'elapsed_seconds': time.monotonic() - started,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'claim_boundary': 'The 246-pair reduction is exact computational evidence, not a Lean theorem. '
                          'The explicit common-box witness is kernel checked separately. '
                          'Neither relaxation establishes feasibility, cap compatibility or the selected-109 exclusion.'}
    with args.output.open('x') as handle:
        json.dump(report, handle, indent=2)
        handle.write('\n')
    print(json.dumps({'retained_pairs': len(retained), 'removed_pairs': len(rejected),
                      'two_three_counts': counts[2, 3], 'seconds': report['elapsed_seconds']}))


if __name__ == '__main__':
    main()
