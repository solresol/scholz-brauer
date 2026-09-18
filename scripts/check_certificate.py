#!/usr/bin/env python3
"""Check an addition-chain index certificate without importing its generator.

Reconstruct exact integer values, require earlier summands and strict growth,
and compare the endpoint and number of additions to explicit expectations.
An additional value-only check verifies star steps without reading pairs.
"""
import argparse
import hashlib
import json
from pathlib import Path


def replay_indices(pairs, *, target, additions):
    if type(target) is not int or target < 1:
        raise ValueError("target must be a positive integer")
    if type(additions) is not int or additions < 0 or len(pairs) != additions:
        raise ValueError("incorrect addition count")
    chain = [1]
    for i, pair in enumerate(pairs, 1):
        if not isinstance(pair, (list, tuple)) or len(pair) != 2:
            raise ValueError(f"step {i}: expected two indices")
        if any(type(j) is not int or not 0 <= j < i for j in pair):
            raise ValueError(f"step {i}: unavailable index")
        value = chain[pair[0]] + chain[pair[1]]
        if value <= chain[-1]:
            raise ValueError(f"step {i}: chain does not increase")
        chain.append(value)
    if chain[-1] != target:
        raise ValueError("incorrect endpoint")
    return chain


def check_star_values(chain):
    """Recover a previous summand by subtraction; ignore all certificate pairs."""
    if not chain or any(type(v) is not int for v in chain) or chain[0] != 1:
        raise ValueError("expected integer values starting at 1")
    previous_values = {1}
    for i in range(1, len(chain)):
        value = chain[i]
        if value <= chain[i - 1] or value - chain[i - 1] not in previous_values:
            raise ValueError(f"step {i}: not a star addition")
        previous_values.add(value)


def check_document(document, *, exponent, additions):
    if type(exponent) is not int or exponent < 1:
        raise ValueError("exponent must be positive")
    if document.get("format") != "addition-chain-indices-v1":
        raise ValueError("unknown format")
    if type(document.get("start")) is not int or document["start"] != 1:
        raise ValueError("incorrect start")
    declared_target = document.get("target", {})
    if (declared_target.get("kind") != "mersenne"
            or type(declared_target.get("exponent")) is not int
            or declared_target["exponent"] != exponent):
        raise ValueError("target declaration differs from requested target")
    if (type(document.get("additions")) is not int
            or document["additions"] != additions):
        raise ValueError("addition declaration differs from requested count")
    # source_chain is provenance only: it is not trusted or needed for replay.
    return replay_indices(document["pairs"], target=(1 << exponent) - 1,
                          additions=additions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--exponent", required=True, type=int)
    parser.add_argument("--additions", required=True, type=int)
    parser.add_argument("--require-star", action="store_true")
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    chain = check_document(json.loads(raw), exponent=args.exponent,
                           additions=args.additions)
    if args.require_star:
        check_star_values(chain)
    print(json.dumps({"certificate_sha256": hashlib.sha256(raw).hexdigest(),
                      "exponent": args.exponent, "additions": len(chain) - 1,
                      "endpoint_bit_length": chain[-1].bit_length(),
                      "exact_endpoint_verified": True,
                      "value_only_star_check": args.require_star,
                      "optimality_proved": False}, indent=2))


if __name__ == "__main__":
    main()
