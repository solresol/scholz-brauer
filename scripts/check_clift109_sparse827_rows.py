"""Replay the (8,27) scan and compare its full rows with the two Lean tables."""
from collections import Counter
from pathlib import Path
import re

from experiment_clift109_gap_slice import classify_slice
from experiment_clift109_outer_boxes import dimensions


def literal_rows(filename, declaration):
    root = Path(__file__).resolve().parents[1] / 'lean/ScholzBrauer'
    source = (root / filename).read_text().split(f'def {declaration} :', 1)[1]
    table = source.split(':=', 1)[1].split(']', 1)[0]
    return [tuple(map(int, re.findall(r'-?\d+', row)))
            for row in re.findall(r'⟨([^⟩]+)⟩', table)]


def main():
    rejected = []
    surviving = []
    counts = Counter()
    for ds, _ in dimensions(6, 1, 108):
        if 8 not in ds or 27 not in ds:
            continue
        free = tuple(x for x in ds if x not in (8, 27))

        def check(t, v, r, s, z, remainder, half):
            points = {x for x in range(109) if remainder >> x & 1}
            isolated = sorted(x for x in points if x-27 not in points and x+27 not in points)
            counts[len(isolated)] += 1
            if isolated:
                assert half is None
                assert ds == (1, ds[1], 8, ds[3], 27, ds[5])
                rejected.append((ds[1], ds[3], ds[5], t, v, r, s, z, isolated[0]))
            else:
                assert half is not None and ds == (1, 5, 8, 11, 27, 54) and t == 1
                surviving.append((v, r, s, z, *(x for x in range(109) if half >> x & 1)))

        classify_slice(8, 27, free, on_fingerprint=check)

    assert sorted(rejected) == sorted(literal_rows('Clift109Isolated.lean', 'isolated827Rows'))
    assert sorted(surviving) == sorted(literal_rows('Clift109TranslatedExceptions.lean',
                                                    'sparse827Rows'))
    print(f'{len(rejected)} isolated rows and {len(surviving)} halves match the Lean tables')
    print('isolated points per fingerprint match:', sorted(counts.items()))


if __name__ == '__main__':
    main()
