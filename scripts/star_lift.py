#!/usr/bin/env python3
"""Brauer lift to an explicit, zero-based summand-index certificate.

For a star step a -> a+b, double M_a exactly b times, then add the
previously stored M_b, where M_k = 2**k - 1. No optimality is assumed.
Only the Python standard library is required (Python >= 3.9).
"""
import argparse
import json
from pathlib import Path


def star_lift(chain):
    """Return pairs whose replay starts at 1 and ends at 2**chain[-1]-1.

    Validate the complete input before generating any output. Length is
    chain[-1] - 1 + len(chain) - 1. The singleton [1] yields no pairs.
    """
    if not chain or any(type(a) is not int for a in chain) or chain[0] != 1:
        raise ValueError("expected an integer chain beginning with 1")
    seen = {1}
    for a, c in zip(chain, chain[1:]):
        if c <= a or c - a not in seen:
            raise ValueError(f"not a star step: {a} -> {c}")
        seen.add(c)

    pairs = []
    mersenne_indices = {1: 0}
    for a, c in zip(chain, chain[1:]):
        b = c - a
        for _ in range(b):
            last = len(pairs)
            pairs.append([last, last])
        pairs.append([len(pairs), mersenne_indices[b]])
        mersenne_indices[c] = len(pairs)
    return pairs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON object with a chain field")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    source = json.loads(args.input.read_text())
    chain = source["chain"]
    pairs = star_lift(chain)
    document = {"format": "addition-chain-indices-v1", "start": 1,
                "target": {"kind": "mersenne", "exponent": chain[-1]},
                "additions": len(pairs), "source_chain": chain,
                "pairs": pairs}
    args.output.write_text(json.dumps(document, separators=(",", ":")) + "\n")
    print(json.dumps({"certificate": str(args.output), "exponent": chain[-1],
                      "additions": len(pairs)}))


if __name__ == "__main__":
    main()
