"""Exact interval-output slice through the relaxed (2,3) compatibility witness."""
import argparse
from collections import Counter
from itertools import permutations
import json
import platform
import time

from experiment_clift109_common_box import compatibility_gap, odd_runs
from experiment_clift109_sink_classifier import classify
from clift109_box_dual import halve


def singleton_choices(points, step):
    """Deletion must split the unique odd run into two even runs."""
    candidates = None
    for first in points:
        if first-step in points:
            continue
        run = [first]
        while run[-1]+step in points:
            run.append(run[-1]+step)
        if len(run) % 2:
            if candidates is not None:
                return set()
            candidates = run[::2]
    return set(candidates or ())


def classify_slice(u, d, free, *, count_translates=False, on_fingerprint=None):
    start = time.monotonic()
    sums = {0}
    for k in (u, d, *free):
        sums |= {x+k for x in sums}
    assert len(sums) == 64
    counts = Counter()
    solutions = []
    digit = [(-1)**(x//d) * 4**(x%d) for x in range(109)]
    target = sum(digit)
    for t in range(109-max(sums)):
        rest = set(range(109)) - {x+t for x in sums}
        counts['role_inputs'] += 24
        if any(odd_runs(rest, step) > 7 for step in (u, d)):
            continue
        counts['odd_run_surviving_inputs'] += 24
        mask = sum(1 << x for x in rest)
        for v in free:
            orders = list(permutations(x for x in free if x != v))
            for r in sorted(rest):
                rect = {r, r+u, r+v, r+u+v}
                if len(rect) != 4 or not rect <= rest:
                    continue
                after = rest - rect
                for s in sorted(after):
                    if s+u not in after:
                        continue
                    six = rect | {s, s+u}
                    rem = mask ^ sum(1 << x for x in six)
                    six_score = sum(digit[x] for x in six)
                    candidates = singleton_choices(rest-six, d)
                    for z in sorted(rest-six):
                        counts['disjoint_position_triples_before_role_expansion'] += 1
                        matches = six_score + digit[z] == target
                        counts['fingerprint_triples_before_role_expansion'] += int(matches)
                        half = halve(rem ^ (1 << z), d)
                        if matches and on_fingerprint is not None:
                            on_fingerprint(t, v, r, s, z, rem ^ (1 << z), half)
                        halvable = half is not None
                        if halvable != (z in candidates):
                            raise ValueError('odd-run singleton selection disagrees with peeling')
                        if not halvable:
                            continue
                        if not matches:
                            raise ValueError('fingerprint dropped a halvable triple')
                        counts['halvable_triples_before_role_expansion'] += 1
                        if count_translates:
                            points = {x for x in range(109) if half >> x & 1}
                            exceptions = six | {z}
                            survives = any(all(x-z+a in points for x in exceptions)
                                           for a in points)
                            counts['translated_exception_triples'] += int(survives)
                        for w, d2, d3 in orders:
                            box = [u, v, w, d, d2, d3, t] + [0]*5
                            solutions.extend(classify(box, r, s, z))
    return dict(counts=counts, solutions=sorted(solutions), free_dimensions=free,
                ordered_steps=[u,d], translations=[0,108-max(sums)],
                python=platform.python_version(), seconds=time.monotonic()-start)


def run(all_roles=False):
    u, v, w, d, d2, d3, *_ = compatibility_gap()['coordinates']
    free = (v, w, d2, d3)
    if not all_roles:
        return classify_slice(u, d, free)
    dimensions = (u, d, *free)
    return [classify_slice(a, b, tuple(k for k in dimensions if k not in (a, b)))
            for a, b in permutations(dimensions, 2)]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--all-roles', action='store_true',
                        help='exhaust every ordered choice of the source and sink steps')
    print(json.dumps(run(parser.parse_args().all_roles), indent=2))
