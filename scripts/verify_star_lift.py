#!/usr/bin/env python3
"""Bounded deterministic verification; no search for optimal chains.

Exhaust all star-chain prefixes of at most six steps and endpoint at most 32,
then test binary star witnesses for 1..256 and the saved 12509 certificate.
"""
import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path
import platform
import time
from zoneinfo import ZoneInfo

from check_12509 import check_chain
from check_certificate import check_document, check_star_values, replay_indices
from star_lift import star_lift


def binary_chain(n):
    chain = [1]
    for bit in bin(n)[3:]:
        chain.append(chain[-1] * 2)
        if bit == "1":
            chain.append(chain[-1] + 1)
    return chain


def star_prefixes(chain=(1,), max_steps=6, max_endpoint=32):
    # Every strictly increasing star extension has exactly this form.
    # Entries are distinct, so enumeration has no duplicate child chains.
    yield list(chain)
    if len(chain) - 1 < max_steps:
        for earlier in chain:
            value = chain[-1] + earlier
            if value <= max_endpoint:
                yield from star_prefixes(chain + (value,), max_steps, max_endpoint)


def verify_lift(source):
    check_star_values(source)
    pairs = star_lift(source)
    expected = source[-1] + len(source) - 2
    values = replay_indices(pairs, target=(1 << source[-1]) - 1,
                            additions=expected)
    check_star_values(values)
    return values


def expect_rejection(function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except ValueError:
        return
    raise AssertionError("invalid input was accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = time.perf_counter()
    run_time = datetime.now(ZoneInfo("Australia/Sydney"))
    root = Path(__file__).resolve().parents[1]

    # Small manually derived answers catch indexing/step-count regressions.
    if star_lift([1]) != [] or verify_lift([1, 2, 3]) != [1, 2, 3, 6, 7]:
        raise AssertionError("hand-derived fixture differs")
    # The generic checker must also accept a valid non-star certificate.
    nonstar = [[0, 0], [1, 1], [2, 1], [3, 3], [4, 0], [4, 4]]
    values = replay_indices(nonstar, target=24, additions=6)
    check_chain(values)
    expect_rejection(check_star_values, values)
    # Non-star chosen parent indices need not imply non-star chain values:
    # the final 6 = 3+3 can also be written as 5+1.
    alternate = [[0, 0], [1, 0], [2, 1], [2, 2]]
    check_star_values(replay_indices(alternate, target=6, additions=4))

    invalid_sources = [[], [2], [True], [1, 2.0], [1, 1], [1, 2, 5],
                       [1, 2, 3, 2], [1, 2, 4, 6, 12, 13, 24]]
    for source in invalid_sources:
        expect_rejection(star_lift, source)
    invalid_pairs = [[[-1, 0]], [[1, 0]], [[True, 0]], [[0.0, 0]],
                     [[0]], [[0, 0, 0]], [[0, 0], [0, 0]]]
    for pairs in invalid_pairs:
        expect_rejection(replay_indices, pairs, target=2, additions=len(pairs))
    expect_rejection(replay_indices, [[0, 0]], target=3, additions=1)
    expect_rejection(replay_indices, [[0, 0]], target=2, additions=2)
    expect_rejection(replay_indices, [], target=True, additions=0)
    expect_rejection(replay_indices, [], target=1, additions=False)

    exhaustive_count = 0
    digest = hashlib.sha256()
    for source in star_prefixes():
        verify_lift(source)
        digest.update((json.dumps(source, separators=(",", ":")) + "\n").encode())
        exhaustive_count += 1
    for n in range(1, 257):
        values = verify_lift(binary_chain(n))
        if n <= 16:
            # The older cubic checker discovers every summand pair from values.
            check_chain(values)

    source = json.loads((root / "data/12509-star.json").read_text())["chain"]
    check_chain(source)  # independently discover parents of the published data
    values = verify_lift(source)
    if len(source) != 19 or source[-1] != 12509 or len(values) != 12527:
        raise AssertionError("unexpected published input or output length")
    cert_path = root / "results/2026-09-18-12509-star-certificate.json"
    raw = cert_path.read_bytes()
    document = json.loads(raw)
    saved_values = check_document(document, exponent=12509, additions=12526)
    check_star_values(saved_values)
    if document["pairs"] != star_lift(source) or saved_values != values:
        raise AssertionError("saved certificate is not reproducible")
    expect_rejection(check_document, document, exponent=12508, additions=12526)
    expect_rejection(check_document, document, exponent=12509, additions=12525)
    # Deliberately damage the final operation: strict-growth checking must fail.
    damaged = dict(document, pairs=document["pairs"][:-1] + [[0, 0]])
    expect_rejection(check_document, damaged, exponent=12509, additions=12526)
    # Provenance is not a proof input; a checker cannot rely on source_chain.
    without_source = dict(document)
    del without_source["source_chain"]
    check_document(without_source, exponent=12509, additions=12526)

    report = {
        "date_australia_sydney": run_time.date().isoformat(),
        "started_at_australia_sydney": run_time.isoformat(),
        "python": platform.python_version(),
        "dependencies": "Python standard library only", "seed": None,
        "exhaustive_star_prefixes": {"max_steps": 6, "max_endpoint": 32,
                                     "count": exhaustive_count,
                                     "input_sha256": digest.hexdigest()},
        "binary_exponents": {"first": 1, "last": 256, "count": 256},
        "all_parent_pair_value_checks": "binary lifts for n=1..16; published star input",
        "negative_checks": 23,
        "published_input": {"exponent": 12509, "additions": 18},
        "lift": {"additions": len(values) - 1, "endpoint_bit_length": values[-1].bit_length(),
                 "exact_endpoint_verified": True, "independent_value_star_check": True,
                 "certificate_sha256": hashlib.sha256(raw).hexdigest()},
        "optimality_proved": False, "scholz_bound_for_12509_proved": False,
        "lean_lift_formalised": False,
        "runtime_seconds": round(time.perf_counter() - started, 6)}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
