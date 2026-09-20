#!/usr/bin/env python3
"""Bounded exact Hansen verification; no optimal-chain or frontier search."""
import argparse
from datetime import datetime
import hashlib
import itertools
import json
from pathlib import Path
import platform
import time
from zoneinfo import ZoneInfo

from check_12509 import check_chain
from check_certificate import check_document, replay_indices
from hansen_lift import checked_plan, find_underlining, hansen_lift
from star_lift import star_lift


ROOT = Path(__file__).resolve().parents[1]
SAVED = ROOT / "results/2026-09-21-12509-hansen-certificate.json"


def addition_prefixes(chain=(1,), max_steps=6, max_endpoint=32):
    """Enumerate every increasing value chain in the finite test family once."""
    yield list(chain)
    if len(chain) - 1 < max_steps:
        successors = {a + b for a in chain for b in chain
                      if chain[-1] < a + b <= max_endpoint}
        for value in sorted(successors):
            yield from addition_prefixes(chain + (value,), max_steps, max_endpoint)


def brute_underlinings(chain):
    """Independent oracle: all masks and all discovered parent pairs.

    Neither the DP nor its checked_plan is used. Return every successful
    marking; this exhaustive oracle is used only for sources <=8 entries.
    """
    parents = check_chain(chain)
    if len(chain) == 1:
        return [[0]], 1
    accepted = []
    count = 0
    for bits in itertools.product((False, True), repeat=len(chain) - 2):
        count += 1
        marks = [0] + [i for i, bit in enumerate(bits, 1) if bit] + [len(chain)-1]
        if all(any(max(k for k in marks if k < i) in pair for pair in pairs)
               for i, pairs in enumerate(parents, 1)):
            accepted.append(marks)
    return accepted, count


def reject(function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except ValueError:
        return 1
    raise AssertionError("invalid input accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    started = time.perf_counter()
    run_time = datetime.now(ZoneInfo("Australia/Sydney"))
    paths = [Path(__file__).resolve(), ROOT / "scripts/hansen_lift.py",
             ROOT / "scripts/check_certificate.py", ROOT / "scripts/check_12509.py",
             ROOT / "scripts/star_lift.py", ROOT / "data/12509-hansen.json", SAVED]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in paths}
    digest = hashlib.sha256()
    counts = {"sources": 0, "masks": 0, "accepted_underlinings": 0,
              "non_hansen_sources": 0, "star_comparisons": 0}
    for chain in addition_prefixes():
        counts["sources"] += 1
        digest.update((json.dumps(chain, separators=(",", ":")) + "\n").encode())
        expected, masks = brute_underlinings(chain)
        counts["masks"] += masks
        found = find_underlining(chain)
        if (found is None) != (not expected) or (found is not None and found not in expected):
            raise AssertionError("DP differs from exhaustive underlining oracle")
        if not expected:
            counts["non_hansen_sources"] += 1
        for marks in expected:
            counts["accepted_underlinings"] += 1
            document = hansen_lift(chain, marks)
            values = check_document(document, exponent=chain[-1],
                                    additions=chain[-1] + len(chain) - 2)
            check_chain(values)  # Recover ALL parent pairs without generator indices.
        if all(chain[i] - chain[i-1] in chain[:i] for i in range(1, len(chain))):
            counts["star_comparisons"] += 1
            old = replay_indices(star_lift(chain), target=(1 << chain[-1])-1,
                                 additions=chain[-1] + len(chain) - 2)
            all_marked = hansen_lift(chain, list(range(len(chain))))
            if old != check_document(all_marked, exponent=chain[-1], additions=len(old)-1):
                raise AssertionError("all-marked Hansen and Brauer values differ")

    # Same endpoint/length, distinct structural classification. These are small
    # Clift examples, not a statement that 29 is a non-Hansen number.
    structural = []
    for chain, expected_hansen in [([1,2,4,8,9,12,17,29], True),
                                    ([1,2,4,8,9,13,16,29], False)]:
        oracle, masks = brute_underlinings(chain)
        found = find_underlining(chain)
        if bool(oracle) != expected_hansen or (found is not None) != expected_hansen:
            raise AssertionError("structural regression differs")
        if found is not None:
            check_document(hansen_lift(chain), exponent=29, additions=35)
        structural.append({"chain": chain, "hansen": expected_hansen,
                           "masks_checked": masks, "underlined_indices": found})

    fixture = json.loads((ROOT / "data/12509-hansen.json").read_text())
    examples = []
    for entry in [fixture, fixture["additional_fixture"]]:
        chain = entry["chain"]
        parents = check_chain(chain)
        if chain[-1] != 12509 or len(parents) != 17:
            raise AssertionError("published input differs")
        document = hansen_lift(chain)
        check_document(document, exponent=12509, additions=12525)
        examples.append({"source": entry["name"], "source_additions": len(parents),
                         "underlined_indices": document["underlined_indices"],
                         "max_shifts": document["max_shifts"],
                         "doublings": sum(document["max_shifts"]),
                         "additions": document["additions"], "exact_endpoint_verified": True})
    document = json.loads(SAVED.read_text())
    if document != hansen_lift(fixture["chain"]):
        raise AssertionError("saved certificate is not reproducible")
    values = check_document(document, exponent=12509, additions=12525)
    without_provenance = {k: document[k] for k in ("format", "start", "target", "additions", "pairs")}
    check_document(without_provenance, exponent=12509, additions=12525)

    negatives = 0
    for bad in [[], [2], [True], [1,2.0], [1,1], [1,3,2]]:
        negatives += reject(find_underlining, bad)
    for bad in [[1,2,5], [1,2,4,8,9,13,16,29]]:
        negatives += reject(hansen_lift, bad)
    for marks in [[], [0], [2], [0,True,2], [0,2,2], [0,3], [0,2,1]]:
        negatives += reject(checked_plan, [1,2,3], marks)
    negatives += reject(checked_plan, fixture["chain"], list(range(18)))
    negatives += reject(hansen_lift, fixture["chain"], max_additions=12524)
    negatives += reject(hansen_lift, [1], max_additions=True)
    negatives += reject(check_document, document, exponent=12508, additions=12525)
    negatives += reject(check_document, document, exponent=12509, additions=12524)
    damaged = dict(document, pairs=document["pairs"][:-1] + [[0,0]])
    negatives += reject(check_document, damaged, exponent=12509, additions=12525)
    if any(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest
           for name, digest in hashes.items()):
        raise ValueError("verification inputs changed during run")
    report = {"started_at_australia_sydney": run_time.isoformat(),
              "weekday_australia_sydney": run_time.strftime("%A"),
              "python": platform.python_version(), "dependencies": "standard library only",
              "seed": None, "input_sha256": hashes,
              "exhaustive_family": dict(counts, max_steps=6, max_endpoint=32,
                                        input_sha256=digest.hexdigest()),
              "structural_regressions": structural, "published_examples": examples,
              "negative_checks": negatives,
              "certificate_sha256": hashes[str(SAVED.relative_to(ROOT))],
              "endpoint_bit_length": values[-1].bit_length(),
              "optimality_proved": False, "scholz_at_12509_proved": False,
              "hansen_lift_formalised_in_lean": False,
              "runtime_seconds": round(time.perf_counter() - started, 6)}
    with args.output.open("x") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
