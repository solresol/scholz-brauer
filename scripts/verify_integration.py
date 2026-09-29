#!/usr/bin/env python3
"""Rerun the small research checks and record their evidence together.

Run from any directory with Python >= 3.9 and the pinned Lake environment.
Includes two bounded exhaustive optimality checks for 12509; no network retrieval.
The output is created only after every check passes; existing reports are refused.
"""
import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import sys
import tempfile
import time
from zoneinfo import ZoneInfo


ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_axioms(output, expected):
    """Fail closed on missing audit entries or nonstandard proof dependencies."""
    entries = re.findall(
        r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|"
        r"does not depend on any axioms)$", output, re.MULTILINE)
    if [name for name, _ in entries] != expected:
        raise ValueError("axiom audit entries differ from Audit.lean")
    allowed = {"propext", "Quot.sound", "Classical.choice"}
    for name, axioms in entries:
        if set(filter(None, (a.strip() for a in axioms.split(",")))) - allowed:
            raise ValueError(f"unapproved axiom in {name}: {axioms}")
    return len(entries)


def compose_12509_evidence(witness, mersenne, research, exclusion):
    """Combine fresh checker results; these summaries are not proof objects.

    The runner must execute the independent checkers first. Reject mismatched
    statements, incomplete searches and a lift too long for the claimed bound.
    This does not establish checker soundness or any Lean theorem.
    """
    def expect(record, key, value):
        actual = record.get(key)
        if type(actual) is not type(value) or actual != value:
            raise ValueError(f"evidence mismatch for {key}: expected {value!r}")

    expect(witness, "endpoint", 12509)
    expect(witness, "additions", 17)
    if not isinstance(research, dict):
        raise ValueError("missing exhaustive research results")
    limit = witness["additions"] - 1
    for name in ("cpp", "python"):
        result = research[name]
        expect(result, "target", witness["endpoint"])
        expect(result, "max_steps", limit)
        expect(result, "status", "exhausted")
        expect(result, "witness", [] if name == "cpp" else None)
    expect(research["cpp"], "prefix", [1])
    if any(type(x) is not int for x in research["cpp"]["prefix"]):
        raise ValueError("invalid search root")
    expect(research["cpp"], "pending_prefixes", [])
    expect(exclusion, "status", "excluded")
    expect(exclusion, "target", witness["endpoint"])
    expect(exclusion, "max_steps", limit)
    expect(mersenne, "exponent", witness["endpoint"])
    expect(mersenne, "exact_endpoint_verified", True)
    additions = mersenne.get("additions")
    rhs = witness["endpoint"] - 1 + witness["additions"]
    if type(additions) is not int or not 0 <= additions <= rhs:
        raise ValueError("Mersenne witness does not establish the Scholz bound")
    return {
        "computational_ell_12509_bounds": [limit + 1, witness["additions"]],
        "scholz_rhs_from_computational_optimality": rhs,
        "checked_mersenne_witness_additions": additions,
        "optimality_computationally_established": True,
        "scholz_at_12509_computationally_established": True,
        "portable_exclusion_certificate_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    started = time.perf_counter()
    run_time = datetime.now(ZoneInfo("Australia/Sydney"))
    commands = []

    def run(argv, cwd=ROOT):
        begin = time.perf_counter()
        result = subprocess.run(argv, cwd=cwd, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=180, check=True)
        commands.append({"argv": argv, "cwd": str(cwd.relative_to(ROOT)),
                         "exit_code": result.returncode,
                         "runtime_seconds": round(time.perf_counter() - begin, 6),
                         "output": result.stdout})
        return result.stdout

    # Record exact inputs, including local modifications beyond the base commit.
    inputs = sorted(set((ROOT / "scripts").glob("*.py"))
                    | set((ROOT / "scripts").glob("*.cpp"))
                    | set((ROOT / "lean").glob("*.lean"))
                    | set((ROOT / "lean/ScholzBrauer").glob("*.lean"))
                    | set((ROOT / "lean/vendor/formal-conjectures").iterdir())
                    | {ROOT / "lean/lean-toolchain", ROOT / "lean/lakefile.toml",
                       ROOT / "lean/lake-manifest.json", ROOT / "data/12509-star.json",
                       ROOT / "data/12509-hansen.json",
                       ROOT / "data/2026-09-24-hansen-sources.json",
                       ROOT / "data/2026-09-26-hansen-shift-sources.json",
                       ROOT / "data/2026-09-27-integration-sources.json",
                       ROOT / "data/2026-09-28-hansen-export-sources.json",
                       ROOT / "data/2026-09-29-hansen-nodes-sources.json",
                       ROOT / "data/2026-09-30-hansen-allocation-sources.json",
                       ROOT / "data/hansen-replay-fixtures.json",
                       ROOT / "results/2026-09-30-29-hansen-allocation.json",
                       ROOT / "results/2026-09-30-12509-hansen-allocation.json",
                       ROOT / "results/2026-09-18-12509-star-certificate.json",
                       ROOT / "results/2026-09-21-12509-hansen-certificate.json",
                       ROOT / "results/2026-09-25-12509-exclusion-certificate.json"})
    hashes = {str(p.relative_to(ROOT)): sha256(p) for p in inputs}
    vendor = ROOT / "lean/vendor/formal-conjectures"
    provenance = json.loads((vendor / "provenance.json").read_text())
    for entry in provenance["files"]:
        if sha256(vendor / Path(entry["path"]).name) != entry["sha256"]:
            raise ValueError(f"vendored source hash mismatch: {entry['path']}")

    witness = json.loads(run([sys.executable, "scripts/check_12509.py"]))
    certificate = json.loads(run([
        sys.executable, "scripts/check_certificate.py",
        "results/2026-09-18-12509-star-certificate.json",
        "--exponent", "12509", "--additions", "12526", "--require-star"]))
    mersenne_path = "results/2026-09-21-12509-hansen-certificate.json"
    mersenne = json.loads(run([
        sys.executable, "scripts/check_certificate.py", mersenne_path,
        "--exponent", "12509", "--additions", "12525"]))
    if mersenne["certificate_sha256"] != hashes[mersenne_path]:
        raise ValueError("Mersenne replay differs from hashed integration input")
    run([sys.executable, "scripts/verify_evidence_composition.py"])
    run([sys.executable, "-O", "scripts/verify_evidence_composition.py"])
    with tempfile.TemporaryDirectory(prefix=".integration-", dir=ROOT) as temporary:
        small = json.loads(run([sys.executable, "scripts/verify_star_lift.py",
                               "--output", str(Path(temporary) / "small.json")]))
        hansen = json.loads(run([sys.executable, "scripts/verify_hansen_lift.py",
                                "--output", str(Path(temporary) / "hansen.json")]))
        export_path = Path(temporary) / "export.json"
        run([sys.executable, "scripts/verify_lean_export.py", "--output", str(export_path)])
        export = json.loads(export_path.read_text())
        run([sys.executable, "-O", "scripts/verify_lean_export.py",
             "--output", str(Path(temporary) / "export-optimized.json")])
        allocation_path = Path(temporary) / "allocation.json"
        run([sys.executable, "scripts/verify_hansen_allocation.py",
             "--output", str(allocation_path)])
        allocation = json.loads(allocation_path.read_text())
        run([sys.executable, "-O", "scripts/verify_hansen_allocation.py",
             "--output", str(Path(temporary) / "allocation-optimized.json")])
        search_path = Path(temporary) / "search.json"
        run([sys.executable, "scripts/verify_search.py", "--research",
             "--output", str(search_path)])
        search = json.loads(search_path.read_text())
        exclusion_path = Path(temporary) / "exclusion.json"
        run([sys.executable, "scripts/verify_exclusion.py",
             "--output", str(exclusion_path)])
        exclusion = json.loads(exclusion_path.read_text())
    computational = compose_12509_evidence(
        witness, mersenne, search["research"], exclusion["saved_12509"])
    if hansen["certificate_sha256"] != mersenne["certificate_sha256"]:
        raise ValueError("Hansen regression and standalone replay used different certificates")
    if small["date_australia_sydney"] < run_time.date().isoformat():
        raise ValueError("small-check report has a stale run date")
    if small["exhaustive_star_prefixes"]["count"] != 842:
        raise ValueError("small-check family changed; review its scope")
    run(["lake", "build"], ROOT / "lean")
    audit = run(["lake", "env", "lean", "Audit.lean"], ROOT / "lean")
    expected = re.findall(r"^#print axioms (\S+)$",
                          (ROOT / "lean/Audit.lean").read_text(), re.MULTILINE)
    if not expected:
        raise ValueError("empty theorem audit")
    audited = check_axioms(audit, expected)
    version = run(["lake", "env", "lean", "--version"], ROOT / "lean").strip()
    pin = (ROOT / "lean/lean-toolchain").read_text().strip().split(":v")[-1]
    if not version.startswith(f"Lean (version {pin},"):
        raise ValueError("running Lean version differs from toolchain pin")
    if any(sha256(ROOT / name) != digest for name, digest in hashes.items()):
        raise ValueError("research inputs changed during verification")

    report = {
        "started_at_australia_sydney": run_time.isoformat(),
        "weekday_australia_sydney": run_time.strftime("%A"),
        "base_commit": run(["git", "rev-parse", "HEAD"]).strip(),
        "python": platform.python_version(), "lean": version, "seed": None,
        "input_sha256": hashes, "vendored_hashes_checked": len(provenance["files"]),
        "audited_theorems": audited, "commands": commands,
        "witness": witness, "certificate": certificate, "small_checks": small,
        "hansen_certificate_replay": mersenne,
        "hansen_checks": hansen, "search_checks": search,
        "lean_export_checks": export,
        "hansen_allocation_checks": allocation,
        "exclusion_certificate_checks": exclusion,
        "claim_boundary": {
            **computational,
            "lean_ell_12509_bounds": [14, 17],
            "target_if_ell_12509_equals_17": 12525,
            "optimality_or_scholz_at_12509_formalised": False,
            "whole_star_lift_formalised": True,
            "lean_mersenne_12509_upper_bound": 12526,
            "hansen_lift_formalised": False,
            "lean_hansen_replay_fixture_exponents": [1, 29],
            "general_index_value_equivalence_formalised": False,
            "hansen_underlining_checker_formalised": True,
            "hansen_latest_marked_anchor_formalised": True,
            "hansen_shift_maximum_and_telescope_formalised": True,
            "positive_shifted_mersenne_injectivity_formalised": True,
            "hansen_sorted_replay_formalised": False,
            "labelled_hansen_allocation_independently_checked": True,
            "general_hansen_allocation_soundness_formalised": False,
            "lean_hansen_12509_shift_budget": 12525,
            "note": "Lean source bounds remain [14,17]. Two exhaustive searches "
                    "exclude every chain of at most 16 additions for 12509. "
                    "Together with the 17-step source and 12525-step Mersenne "
                    "certificate, this establishes the numerical Scholz instance "
                    "computationally; the exclusion is not a Lean proof."},
        "runtime_seconds": round(time.perf_counter() - started, 6)}
    with args.output.open("x") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"report": str(args.output), "audited_theorems": audited,
                      "runtime_seconds": report["runtime_seconds"]}))


if __name__ == "__main__":
    main()
