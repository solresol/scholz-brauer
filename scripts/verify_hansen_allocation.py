#!/usr/bin/env python3
"""Bounded allocation regressions, independent small oracle and saved readback."""
import argparse
from copy import deepcopy
from datetime import datetime
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time
from zoneinfo import ZoneInfo

from check_hansen_allocation import check_allocation
from hansen_allocation import allocate
from hansen_lift import hansen_lift
from verify_hansen_lift import addition_prefixes, brute_underlinings


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = [ROOT / "results/2026-09-30-29-hansen-allocation.json",
            ROOT / "results/2026-09-30-12509-hansen-allocation.json"]


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def reject(function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except ValueError:
        return
    raise AssertionError("invalid input accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    started = time.perf_counter()
    now = datetime.now(ZoneInfo("Australia/Sydney"))
    paths = list((ROOT / "scripts").glob("*.py")) + FIXTURES + [
        ROOT / "data/12509-hansen.json", ROOT / "data/hansen-replay-fixtures.json",
        ROOT / "data/2026-09-30-hansen-allocation-sources.json",
        ROOT / "results/2026-09-21-12509-hansen-certificate.json"]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted(paths)}

    def compare(chain, marks=None):
        document = allocate(chain, marks)
        summary, certificate = check_allocation(document, exponent=chain[-1],
                                               additions=chain[-1] + len(chain) - 2)
        old = hansen_lift(chain, marks)
        require(certificate == {key: old[key] for key in certificate},
                "label compiler differs from existing integer generator")
        return summary, document, certificate

    counts = {"sources": 0, "masks": 0, "accepted_underlinings": 0,
              "non_hansen_sources": 0}
    for chain in addition_prefixes():
        counts["sources"] += 1
        markings, masks = brute_underlinings(chain)
        counts["masks"] += masks
        if not markings:
            counts["non_hansen_sources"] += 1
            reject(allocate, chain)
        for marks in markings:
            compare(chain, marks)
            counts["accepted_underlinings"] += 1

    interleaved = [1, 2, 4, 8, 9, 12, 17, 29]
    fixture = json.loads((ROOT / "data/12509-hansen.json").read_text())
    examples = []
    for chain in ([1], interleaved, fixture["chain"], fixture["additional_fixture"]["chain"]):
        summary, document, certificate = compare(chain)
        examples.append(summary)
        if chain == fixture["chain"]:
            old = json.loads((ROOT / "results/2026-09-21-12509-hansen-certificate.json").read_text())
            require(certificate == {k: old[k] for k in certificate}, "saved replay differs")
        if chain in (interleaved, fixture["chain"]):
            path = FIXTURES[0 if chain == interleaved else 1]
            require(json.loads(path.read_text()) == document, "saved allocation differs")
        # A labelled graph has no prescribed serialization order.
        document["nodes"].reverse()
        reordered, recert = check_allocation(document, exponent=chain[-1],
                                            additions=chain[-1] + len(chain) - 2)
        require(reordered == summary and recert == certificate, "row order affects replay")

    baseline = allocate(interleaved)
    damaged_cases = []
    def damage(name, edit):
        value = deepcopy(baseline)
        edit(value)
        reject(check_allocation, value, exponent=29, additions=35)
        damaged_cases.append(name)

    for key, value in [("format", "wrong"), ("target_exponent", 28),
                       ("target_exponent", True), ("additions", 34),
                       ("additions", 35.0), ("source_chain", None),
                       ("source_chain", [True, 2, 4, 8, 9, 12, 17, 29]),
                       ("source_chain", [1, 2, 4, 8, 9, 13, 16, 29]),
                       ("source_chain", [1, 2, 4, 8, 9, 12, 17, 30]),
                       ("underlined_indices", [0, 1, 2, 3, 4, 6, 7]),
                       ("underlined_indices", [0, 1, 2, 3, 6]),
                       ("underlined_indices", [False, 1, 2, 3, 6, 7]),
                       ("underlined_indices", [0, 1, 2, 3, 3, 6, 7]),
                       ("shift_caps", [1, 2, 4, 4, 8, 0, 12, 0]),
                       ("nodes", None)]:
        damage(f"{key}={value!r}", lambda d, k=key, v=value: d.__setitem__(k, v))
    damage("missing node", lambda d: d["nodes"].pop())
    damage("extra node", lambda d: d["nodes"].append(deepcopy(d["nodes"][-1])))
    damage("duplicate replacing node", lambda d: d["nodes"].__setitem__(4, deepcopy(d["nodes"][3])))
    damage("missing seed", lambda d: d["nodes"].__setitem__(0, deepcopy(d["nodes"][1])))
    damage("seed dependencies", lambda d: d["nodes"][0].__setitem__("summands", [[1, 0], [1, 0]]))
    damage("seed summands field absent", lambda d: d["nodes"][0].pop("summands"))
    damage("boolean cap", lambda d: d["shift_caps"].__setitem__(0, True))
    for field, value in [("label", [0, 0]), ("label", [True, 1]),
                         ("label", [1, 999999999]), ("label", [1, -1]),
                         ("label", [1]), ("summands", None),
                         ("summands", [[1, 1], [1, 1]]),
                         ("summands", [[1, 999999999], [1, 0]]),
                         ("summands", [[True, 0], [1, 0]]),
                         ("summands", [[1, 0]])]:
        damage(f"node {field}={value!r}",
               lambda d, f=field, v=value: d["nodes"][1].__setitem__(f, v))
    base_index = next(i for i, row in enumerate(baseline["nodes"]) if row["label"] == [17, 0])
    damage("wrong base dependency", lambda d: d["nodes"][base_index].__setitem__(
        "summands", [[8, 8], [9, 0]]))
    for key in baseline:
        damage("missing " + key, lambda d, k=key: d.pop(k))

    generator_negatives = 0
    for source in (None, [], [True], [2], [1, 1], [1, 3],
                   [1, 2, 4, 8, 9, 13, 16, 29], [1, 10**100]):
        reject(allocate, source)
        generator_negatives += 1
    for marks in ([], [0], [0, True, 7], [0, 1, 2, 3, 4, 6, 7]):
        reject(allocate, interleaved, marks)
        generator_negatives += 1
    budget_cases = 0
    for kwargs in ({"max_exponent": 28}, {"max_nodes": 35},
                   {"max_exponent": True}, {"max_nodes": 0}):
        reject(allocate, interleaved, **kwargs)
        reject(check_allocation, baseline, exponent=29, additions=35, **kwargs)
        budget_cases += 2
    exact = allocate(interleaved, max_exponent=29, max_nodes=36)
    check_allocation(exact, exponent=29, additions=35, max_exponent=29, max_nodes=36)
    for exponent, additions in [(28, 35), (29, 34), (True, 35), (29, True),
                                (10**100, 35), (29, 10**100)]:
        reject(check_allocation, baseline, exponent=exponent, additions=additions)
        budget_cases += 1

    commands = []
    with tempfile.TemporaryDirectory(prefix=".allocation-", dir=ROOT) as temporary:
        src = Path(temporary) / "source.json"
        dst = Path(temporary) / "allocation.json"
        src.write_text(json.dumps({"chain": interleaved}))
        def run(argv, succeeds):
            result = subprocess.run([sys.executable] + argv, cwd=ROOT, text=True,
                                    capture_output=True, timeout=30)
            require((result.returncode == 0) == succeeds, "CLI exit status differs")
            commands.append({"argv": [sys.executable] + argv, "exit_code": result.returncode,
                             "stdout": result.stdout, "stderr": result.stderr})
        generation = ["scripts/hansen_allocation.py", str(src), str(dst)]
        run(generation, True)
        original = dst.read_bytes()
        run(["scripts/check_hansen_allocation.py", str(dst), "--exponent", "29",
             "--additions", "35"], True)
        run(generation, False)
        require(dst.read_bytes() == original, "overwrite refusal changed output")
        dst.unlink()
        run(generation + ["--max-nodes", "35"], False)
        require(not dst.exists(), "budget failure created output")
        src.write_text(json.dumps({"chain": [1, 2, 4, 8, 9, 13, 16, 29]}))
        run(generation, False)
        require(not dst.exists(), "non-Hansen rejection created output")
    require(all(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest
                for name, digest in hashes.items()), "verification inputs changed")
    report = {"started_at_australia_sydney": now.isoformat(),
              "weekday_australia_sydney": now.strftime("%A"),
              "python": platform.python_version(), "dependencies": "standard library only",
              "seed": None, "input_sha256": hashes,
              "budgets": {"max_exponent": 16384, "max_nodes": 20000, "cli_max_bytes": 4000000},
              "exhaustive_family": dict(counts, max_steps=6, max_endpoint=32),
              "examples": examples, "corruptions_rejected": damaged_cases,
              "generator_negatives": generator_negatives, "budget_and_expectation_negatives": budget_cases,
              "cli_checks": commands, "source_optimality_checked": False,
              "general_allocation_soundness_formalised": False,
              "runtime_seconds": round(time.perf_counter() - started, 6)}
    with args.output.open("x") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"report": str(args.output), "small_underlinings": counts["accepted_underlinings"],
                      "corruptions_rejected": len(damaged_cases),
                      "runtime_seconds": report["runtime_seconds"]}))


if __name__ == "__main__":
    main()
