#!/usr/bin/env python3
"""Hansen underlining and explicit Mersenne lift, using exact integers.

Criterion and edge labelling: Neill Clift, ScholzBrauer.html, accessed
2026-09-21. See results/2026-09-21-hansen-lift.md for the construction proof.
Classification is existential over summands of the given values, not over
one preselected formal parent list. No optimality assumption is made.
"""
import argparse
import json
from pathlib import Path


def validate_values(chain):
    if (not chain or any(type(v) is not int for v in chain)
            or chain[0] != 1 or any(a >= b for a, b in zip(chain, chain[1:]))):
        raise ValueError("expected strictly increasing integer values starting at 1")


def find_underlining(chain):
    """Return underlined indices, or None if no underlining exists.

    Dynamic programming keeps one history per largest underlined index.
    Future feasibility depends only on this index and the fixed source prefix,
    so merging histories loses no solutions. At most len(chain) states survive
    per step; both marking choices are explored, including the last entry.
    """
    validate_values(chain)
    states = {0: [0]}
    earlier = {1}
    for i, value in enumerate(chain[1:], 1):
        following = {}
        for anchor, history in states.items():
            if value - chain[anchor] in earlier:
                following.setdefault(anchor, history)
                following.setdefault(i, history + [i])
        states = following
        earlier.add(value)
    return states.get(len(chain) - 1)


def checked_plan(chain, underlined):
    """Validate a marking and return oriented parents and max stored shifts.

    Each new exponent is a_anchor + a_other, where anchor is the largest
    earlier underlined index. Store M_anchor shifted by a_other; M_other is
    used unshifted. Store every intermediate doubling needed by any consumer.
    """
    validate_values(chain)
    if (not isinstance(underlined, (list, tuple)) or not underlined
            or any(type(i) is not int or not 0 <= i < len(chain) for i in underlined)
            or underlined[0] != 0 or underlined[-1] != len(chain) - 1
            or any(a >= b for a, b in zip(underlined, underlined[1:]))):
        raise ValueError("expected increasing underlined indices including both endpoints")
    marks = set(underlined)
    earlier = {1: 0}
    anchor = 0
    parents = []
    shifts = [0] * len(chain)
    for i, value in enumerate(chain[1:], 1):
        other = earlier.get(value - chain[anchor])
        if other is None:
            raise ValueError(f"step {i} does not use the latest underlined value")
        parents.append([anchor, other])
        shifts[anchor] = max(shifts[anchor], chain[other])
        earlier[value] = i
        if i in marks:
            anchor = i
    if sum(shifts) != chain[-1] - 1:
        raise AssertionError("underlined shift counts did not telescope")
    return parents, shifts


def hansen_lift(chain, underlined=None, *, max_additions=100000):
    """Return an ordinary index certificate with exactly n-1+r additions.

    A size budget is checked before allocating large integers. The output is
    numerically sorted so every positive summand precedes its result. Distinct
    odd parts M_a guarantee there are no duplicate generated values.
    """
    validate_values(chain)
    if type(max_additions) is not int or max_additions < 0:
        raise ValueError("max_additions must be a nonnegative integer")
    additions = chain[-1] + len(chain) - 2
    if additions > max_additions:
        raise ValueError("lift exceeds addition budget")
    if underlined is None:
        underlined = find_underlining(chain)
        if underlined is None:
            raise ValueError("source has no Hansen underlining")
    parents, shifts = checked_plan(chain, underlined)
    nodes = {}
    for i, exponent in enumerate(chain):
        base = (1 << exponent) - 1
        for shift in range(shifts[i] + 1):
            value = base << shift
            if shift:
                summands = (value // 2, value // 2)
            elif i:
                anchor, other = parents[i - 1]
                summands = (((1 << chain[anchor]) - 1) << chain[other],
                            (1 << chain[other]) - 1)
            else:
                summands = None
            if value in nodes:
                raise AssertionError("duplicate node")
            nodes[value] = summands
    values = sorted(nodes)
    indices = {value: i for i, value in enumerate(values)}
    pairs = []
    for value in values[1:]:
        left, right = nodes[value]
        if left not in indices or right not in indices or left + right != value:
            raise AssertionError("unavailable or incorrect summands")
        pairs.append([indices[left], indices[right]])
    if len(pairs) != additions or values[-1] != (1 << chain[-1]) - 1:
        raise AssertionError("incorrect lift size or endpoint")
    return {"format": "addition-chain-indices-v1", "start": 1,
            "target": {"kind": "mersenne", "exponent": chain[-1]},
            "additions": additions, "source_chain": list(chain),
            "underlined_indices": list(underlined), "source_parents": parents,
            "max_shifts": shifts, "pairs": pairs}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON object with a chain field")
    parser.add_argument("output", type=Path)
    parser.add_argument("--max-additions", type=int, default=100000)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    source = json.loads(args.input.read_text())
    document = hansen_lift(source["chain"], max_additions=args.max_additions)
    with args.output.open("x") as output:
        output.write(json.dumps(document, separators=(",", ":")) + "\n")
    print(json.dumps({"certificate": str(args.output),
                      "exponent": document["target"]["exponent"],
                      "additions": document["additions"]}))


if __name__ == "__main__":
    main()
