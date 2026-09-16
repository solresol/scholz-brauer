#!/usr/bin/env python3
"""Independently check the Lean fixture with Python integer arithmetic.

This checks one witness, not an exhaustive search or optimality certificate.
It deliberately ignores the summand-pair certificate and discovers all valid
parents directly from the chain's earlier entries.
"""
import ast
import json
from pathlib import Path
import re
import time


def check_chain(chain):
    if not chain or any(type(x) is not int for x in chain) or chain[0] != 1:
        raise ValueError("chain must start at 1")
    parents = []
    for i, value in enumerate(chain[1:], 1):
        if value <= chain[i - 1]:
            raise ValueError(f"step {i} is not a strictly increasing integer")
        matches = [(j, k) for j in range(i) for k in range(j, i)
                   if chain[j] + chain[k] == value]
        if not matches:
            raise ValueError(f"step {i} has no earlier summands")
        parents.append(matches)
    return parents


def main():
    started = time.perf_counter()
    root = Path(__file__).resolve().parents[1]
    source = (root / "lean/ScholzBrauer/Example12509.lean").read_text()
    match = re.search(r"def chain12509 : List ℕ :=\s*(\[[^\]]*\])", source)
    if match is None:
        raise ValueError("chain12509 literal not found")
    chain = ast.literal_eval(match.group(1))
    parents = check_chain(chain)
    if chain[-1] != 12509 or len(parents) != 17:
        raise ValueError("unexpected endpoint or length")
    nonstar = [i for i, ps in enumerate(parents, 1)
               if not any(i - 1 in pair for pair in ps)]
    if nonstar != [6]:
        raise ValueError(f"unexpected non-star steps: {nonstar}")
    for bad in ([], [2], [1, 1], [1, 2, 5], [1, 2, 3, 2], [True], [1, 2.0]):
        try:
            check_chain(bad)
        except ValueError:
            pass
        else:
            raise AssertionError(f"invalid fixture accepted: {bad}")
    print(json.dumps({"endpoint": chain[-1], "additions": len(parents),
                      "nonstar_step_indices_zero_based": nonstar,
                      "parents_zero_based": parents,
                      "negative_checks": 7, "seed": None,
                      "exhaustive_search": False,
                      "optimality_proved": False,
                      "scholz_bound_proved": False,
                      "runtime_seconds": round(time.perf_counter() - started, 6)}, indent=2))


if __name__ == "__main__":
    main()
