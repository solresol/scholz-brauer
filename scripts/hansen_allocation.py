#!/usr/bin/env python3
"""Expose Hansen nodes (source exponent, shift) and labelled dependencies.

This generator allocates labels only, never large Mersenne integers. The
independent check_hansen_allocation.py validates the allocation and sorts it.
"""
import argparse
import json
from pathlib import Path

from hansen_lift import checked_plan, find_underlining, validate_values


def allocate(chain, marks=None, *, max_exponent=16384, max_nodes=20000):
    if not isinstance(chain, (list, tuple)):
        raise ValueError("expected source list")
    validate_values(chain)
    for bound in (max_exponent, max_nodes):
        if type(bound) is not int or bound < 1:
            raise ValueError("budgets must be positive integers")
    if chain[-1] > max_exponent or chain[-1] + len(chain) - 1 > max_nodes:
        raise ValueError("allocation exceeds budget")
    if marks is None:
        marks = find_underlining(chain)
        if marks is None:
            raise ValueError("source has no Hansen underlining")
    parents, caps = checked_plan(chain, marks)
    nodes = []
    for i, exponent in enumerate(chain):
        for shift in range(caps[i] + 1):
            if shift:
                summands = [[exponent, shift - 1], [exponent, shift - 1]]
            elif i:
                anchor, other = parents[i - 1]
                summands = [[chain[anchor], chain[other]], [chain[other], 0]]
            else:
                summands = None
            nodes.append({"label": [exponent, shift], "summands": summands})
    return {"format": "hansen-labelled-allocation-v1", "source_chain": list(chain),
            "underlined_indices": list(marks), "shift_caps": caps,
            "target_exponent": chain[-1], "additions": len(nodes) - 1,
            "nodes": nodes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON with chain and optional underlined_indices")
    parser.add_argument("output", type=Path)
    parser.add_argument("--max-exponent", type=int, default=16384)
    parser.add_argument("--max-nodes", type=int, default=20000)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if args.input.stat().st_size > 4_000_000:
        raise ValueError("input exceeds byte budget")
    source = json.loads(args.input.read_text())
    result = allocate(source["chain"], source.get("underlined_indices"),
                      max_exponent=args.max_exponent, max_nodes=args.max_nodes)
    with args.output.open("x") as output:
        output.write(json.dumps(result, separators=(",", ":")) + "\n")
    print(json.dumps({"allocation": str(args.output), "nodes": len(result["nodes"]),
                      "exponent": result["target_exponent"]}))


if __name__ == "__main__":
    main()
