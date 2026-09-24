#!/usr/bin/env python3
"""Generate a portable exclusion DAG; never emit one on a witness or budget stop.

Repeated proof syntax is shared, NOT search states or checked conclusions.
The independent checker must check every occurrence in its own chain context.
See results/2026-09-25-exclusion-certificate.md for the rules and soundness argument.
"""
import argparse
import json
from pathlib import Path
import time


def generate(target, max_steps, node_budget=2000000):
    if (type(target) is not int or not 1 <= target <= 2**30
            or type(max_steps) is not int or not 0 <= max_steps <= 32
            or type(node_budget) is not int or node_budget < 0):
        raise ValueError("require target in 1..2^30, steps in 0..32, nonnegative budget")
    nodes, interned = [], {}
    visited = 0
    witness = None

    def intern(key):
        if key not in interned:
            interned[key] = len(nodes)
            nodes.append([key[0], [list(edge) for edge in key[1]]]
                         if key[0] == "split" else [key[0]])
        return interned[key]

    class Stop(Exception):
        pass

    def visit(chain, left):
        nonlocal visited, witness
        if visited == node_budget:
            raise Stop
        visited += 1
        if chain[-1] == target:
            witness = chain
            raise Stop
        if chain[-1] * 2**left < target:
            return intern(("bound",))
        if left == 1:
            earlier = set(chain)
            for value in chain:
                if target - value in earlier:
                    witness = chain + [target]
                    raise Stop
            return intern(("gap",))
        # With last < target, the doubling rule already handles left == 0.
        lower = (target + 2**(left-1) - 1) // 2**(left-1)
        choices = sorted({a+b for a in chain for b in chain
                          if chain[-1] < a+b <= target and a+b >= lower})
        edges = tuple((s, visit(chain + [s], left-1)) for s in choices)
        return intern(("split", edges))

    started = time.perf_counter()
    try:
        root = visit([1], max_steps)
        status = "excluded"
        certificate = {"format": "addition-chain-exclusion-v1", "target": target,
                       "max_steps": max_steps, "nodes": nodes, "root": root}
    except Stop:
        status = "witness" if witness is not None else "budget"
        certificate = None
    return {"status": status, "visited": visited, "node_budget": node_budget,
            "witness": witness, "certificate": certificate,
            "runtime_seconds": round(time.perf_counter()-started, 6)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", type=int)
    parser.add_argument("max_steps", type=int)
    parser.add_argument("--node-budget", type=int, default=2000000)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    result = generate(args.target, args.max_steps, args.node_budget)
    certificate = result.pop("certificate")
    if certificate is not None:
        with args.output.open("x") as out:
            out.write(json.dumps(certificate, separators=(",", ":")) + "\n")
        result["certificate_path"] = str(args.output)
        result["distinct_nodes"] = len(certificate["nodes"])
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
