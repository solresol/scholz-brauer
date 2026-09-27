#!/usr/bin/env python3
"""Check bounded index-to-value exports; Lean build is a separate required check."""
import argparse
import ast
from copy import deepcopy
from datetime import datetime
import hashlib
import json
from pathlib import Path
import platform
import re
import time
from zoneinfo import ZoneInfo

from export_lean_certificate import HEADER, FOOTER, render_fixture, value_certificate
from hansen_lift import hansen_lift
from verify_hansen_lift import addition_prefixes, brute_underlinings, reject


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "data/hansen-replay-fixtures.json"
LEAN = ROOT / "lean/ScholzBrauer/HansenReplayFixtures.lean"


def readback(text, name, exponent, additions):
    """Read emitted literals and replay using summand membership, not indices."""
    base = "fixture_" + name
    steps = ast.literal_eval(re.search(
        rf"def {base}_steps : List Step :=\s*(\[.*?\])", text, re.S).group(1))
    expected = ast.literal_eval(re.search(
        rf"def {base}_values : List ℕ :=\s*(\[.*?\])", text, re.S).group(1))
    values = [1]
    available = {1}
    for a, b in steps:
        if a not in available or b not in available or a + b <= values[-1]:
            raise ValueError("emitted value replay failed")
        values.append(a + b)
        available.add(a + b)
    if values != expected or len(steps) != additions or values[-1] != (1 << exponent) - 1:
        raise ValueError("emitted values, endpoint or count differ")
    # Bind the numerical theorem statement to the external test expectation.
    statement = f"theorem {base}_bound : additionChainLength (2 ^ {exponent} - 1) ≤ {additions} :="
    if statement not in text:
        raise ValueError("emitted bound statement differs")
    return values


def fixture_module():
    suite = json.loads(SUITE.read_text())
    source = HEADER
    cases = []
    names = set()
    for case in suite["cases"]:
        name, chain = case["name"], case["source_chain"]
        if name in names:
            raise ValueError("duplicate fixture name")
        names.add(name)
        exponent, additions = chain[-1], chain[-1] + len(chain) - 2
        document = hansen_lift(chain, case["underlined_indices"], max_additions=128)
        rendered = render_fixture(document, name=name, exponent=exponent, additions=additions)
        values = readback(rendered, name, exponent, additions)
        source += rendered
        cases.append({"name": name, "exponent": exponent, "additions": additions,
                      "underlined_indices": document["underlined_indices"],
                      "max_shifts": document["max_shifts"], "values": values,
                      "index_certificate": document})
    return source + FOOTER, cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--emit-fixtures", type=Path,
                        help="write regenerated Lean source to a fresh comparison path")
    args = parser.parse_args()
    if args.output.exists() or (args.emit_fixtures and args.emit_fixtures.exists()):
        raise FileExistsError("output already exists")
    started = time.perf_counter()
    run_time = datetime.now(ZoneInfo("Australia/Sydney"))
    source, cases = fixture_module()
    if source != LEAN.read_text():
        raise ValueError("saved Lean fixtures differ from deterministic export")
    # This particular fixture must actually interleave two Mersenne base nodes
    # inside the 255 doubling family, rather than merely reach the right endpoint.
    interleaved = next(case for case in cases if case["name"] == "interleaved29")
    values = interleaved["values"]
    for window in ([510, 511, 1020], [4080, 4095, 8160]):
        i = values.index(window[0])
        if values[i:i + 3] != window:
            raise ValueError("interleaving regression absent")

    counts = {"sources": 0, "masks": 0, "exported_underlinings": 0}
    digest = hashlib.sha256()
    for chain in addition_prefixes():
        counts["sources"] += 1
        markings, masks = brute_underlinings(chain)
        counts["masks"] += masks
        for marks in markings:
            document = hansen_lift(chain, marks)
            exponent, additions = chain[-1], chain[-1] + len(chain) - 2
            text = render_fixture(document, name="small", exponent=exponent, additions=additions)
            readback(text, "small", exponent, additions)
            digest.update(text.encode())
            counts["exported_underlinings"] += 1
    if counts != {"sources": 1051, "masks": 30582, "exported_underlinings": 5248}:
        raise ValueError("small test family changed")

    good = interleaved["index_certificate"]
    negatives = 0
    for key, replacement in [("format", "unknown"), ("start", True),
            ("target", None), ("target", {"kind": "mersenne", "exponent": 28}),
            ("additions", 34), ("additions", True), ("pairs", None),
            ("pairs", good["pairs"][:-1])]:
        bad = dict(good, **{key: replacement})
        negatives += reject(value_certificate, bad, exponent=29, additions=35)
    for pair in [[0, 1], [-1, 0], [True, 0], [0.0, 0], [0], [0, 0, 0]]:
        bad = deepcopy(good)
        bad["pairs"][0] = pair
        negatives += reject(value_certificate, bad, exponent=29, additions=35)
    bad = deepcopy(good)
    bad["pairs"][-1] = [0, 0]
    negatives += reject(value_certificate, bad, exponent=29, additions=35)
    # Resource limits are enforced even when no replayable document is supplied.
    for exponent, additions in [(0, 0), (65, 0), (12509, 12525),
                                (True, 0), (1, -1), (1, 129), (1, True)]:
        negatives += reject(value_certificate, {}, exponent=exponent, additions=additions)
    for name in ["", "bad-name", "x\naxiom bad : False", "a" * 65]:
        negatives += reject(render_fixture, good, name=name, exponent=29, additions=35)
    # Independent readback catches both damaged literals and a changed bound.
    rendered = render_fixture(good, name="test", exponent=29, additions=35)
    negatives += reject(readback, rendered.replace("(1, 1)", "(1, 2)", 1), "test", 29, 35)
    negatives += reject(readback, rendered.replace("≤ 35", "≤ 34"), "test", 29, 35)
    # Provenance is not proof: removing it must not affect the export.
    bare = {key: good[key] for key in ("format", "start", "target", "additions", "pairs")}
    if render_fixture(bare, name="test", exponent=29, additions=35) != rendered:
        raise ValueError("export unexpectedly depends on source provenance")

    if args.emit_fixtures:
        with args.emit_fixtures.open("x") as output:
            output.write(source)
    report = {"started_at_australia_sydney": run_time.isoformat(),
              "weekday_australia_sydney": run_time.strftime("%A"),
              "python": platform.python_version(), "seed": None,
              "limits": {"max_exponent": 64, "max_additions": 128},
              "exhaustive_family": dict(counts, max_source_steps=6, max_endpoint=32,
                                        rendered_sha256=digest.hexdigest()),
              "negative_checks": negatives, "fixtures": cases,
              "fixture_source_sha256": hashlib.sha256(source.encode()).hexdigest(),
              "lean_build_run_by_this_script": False,
              "general_format_equivalence_proved": False,
              "hansen_lift_formalised": False,
              "runtime_seconds": round(time.perf_counter() - started, 6)}
    with args.output.open("x") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in
                     ("exhaustive_family", "negative_checks", "runtime_seconds")}))


if __name__ == "__main__":
    main()
