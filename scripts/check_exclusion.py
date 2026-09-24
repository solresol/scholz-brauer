#!/usr/bin/env python3
"""Independent exact exclusion-DAG checker; imports no generator/search code.

Acceptance excludes every increasing value chain from [1] with at most the
specified number of additions. This Python checker is not a Lean theorem.
"""
import argparse
import json
from pathlib import Path
import time


def check_exclusion(document, *, target, max_steps, visit_budget=2000000):
    def require(condition, message):
        if not condition:
            raise ValueError(message)

    def natural(x):
        return type(x) is int and x >= 0

    require(natural(target) and 1 <= target <= 2**30, "invalid expected target")
    require(natural(max_steps) and max_steps <= 32, "invalid expected step limit")
    require(natural(visit_budget), "invalid checker budget")
    require(type(document) is dict and set(document) ==
            {"format", "target", "max_steps", "nodes", "root"}, "invalid fields")
    require(document["format"] == "addition-chain-exclusion-v1", "unknown format")
    require(type(document["target"]) is int and document["target"] == target
            and type(document["max_steps"]) is int
            and document["max_steps"] == max_steps, "statement mismatch")
    nodes, root = document["nodes"], document["root"]
    require(type(nodes) is list and len(nodes) > 0, "empty or invalid node table")
    require(natural(root) and root == len(nodes)-1, "root must be final node")
    for index, node in enumerate(nodes):
        require(type(node) is list and len(node) > 0, "invalid node")
        require(node == ["bound"] or node == ["gap"]
                or (len(node) == 2 and node[0] == "split" and type(node[1]) is list),
                "invalid rule")
        if node[0] == "split":
            previous = 0
            for edge in node[1]:
                require(type(edge) is list and len(edge) == 2, "invalid edge")
                value, reference = edge
                require(natural(value) and previous < value <= target,
                        "unsorted, repeated or out-of-range child")
                require(natural(reference) and reference < index,
                        "reference must point strictly backwards")
                previous = value

    visited, used = 0, set()
    counts = {"bound": 0, "gap": 0, "split": 0}

    def check(index, chain, left):
        nonlocal visited
        if visited == visit_budget:
            raise TimeoutError("checker budget reached; no exclusion accepted")
        visited += 1
        used.add(index)
        require(chain[-1] != target, "certificate tries to exclude a reached target")
        node = nodes[index]
        counts[node[0]] += 1
        if node[0] == "bound":
            require(chain[-1] * (1 << left) < target, "false doubling bound")
        elif node[0] == "gap":
            require(left == 1, "gap rule requires exactly one remaining step")
            # Deliberately use triangular pairs, independently of the generator's
            # complement test. No restriction to the most recent summand.
            require(all(chain[i] + chain[j] != target
                        for i in range(len(chain)) for j in range(i+1)),
                    "target has available summands")
        else:
            require(left > 0, "split after step limit")
            # Coverage is checked anew: explicit edges cannot omit any feasible
            # next VALUE. Dropped choices cannot reach target even by doubling.
            possible = set()
            for i, a in enumerate(chain):
                for b in chain[:i+1]:
                    value = a+b
                    if chain[-1] < value <= target and value * (1 << (left-1)) >= target:
                        possible.add(value)
            require([edge[0] for edge in node[1]] == sorted(possible),
                    "split does not cover exactly the feasible next values")
            for value, child in node[1]:
                # DO NOT cache by child id: shared syntax does not establish
                # the same conclusion for a different prefix or step count.
                check(child, chain + [value], left-1)

    started = time.perf_counter()
    check(root, [1], max_steps)
    require(len(used) == len(nodes), "unreachable nodes in certificate")
    return {"status": "excluded", "target": target, "max_steps": max_steps,
            "distinct_nodes": len(nodes), "checked_occurrences": visited,
            "rule_occurrences": counts, "visit_budget": visit_budget,
            "runtime_seconds": round(time.perf_counter()-started, 6),
            "lean_proof": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--target", type=int, required=True)
    parser.add_argument("--max-steps", type=int, required=True)
    parser.add_argument("--visit-budget", type=int, default=2000000)
    args = parser.parse_args()
    result = check_exclusion(json.loads(args.certificate.read_text()),
                             target=args.target, max_steps=args.max_steps,
                             visit_budget=args.visit_budget)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
