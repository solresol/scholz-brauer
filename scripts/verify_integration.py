#!/usr/bin/env python3
"""Rerun the small research checks and record their evidence together.

Run from any directory with Python >= 3.9 and the pinned Lake environment.
No optimality search, new mathematical proof, or network retrieval is performed.
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
                    | set((ROOT / "lean").glob("*.lean"))
                    | set((ROOT / "lean/ScholzBrauer").glob("*.lean"))
                    | set((ROOT / "lean/vendor/formal-conjectures").iterdir())
                    | {ROOT / "lean/lean-toolchain", ROOT / "lean/lakefile.toml",
                       ROOT / "lean/lake-manifest.json", ROOT / "data/12509-star.json",
                       ROOT / "data/12509-hansen.json",
                       ROOT / "results/2026-09-18-12509-star-certificate.json",
                       ROOT / "results/2026-09-21-12509-hansen-certificate.json"})
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
    with tempfile.TemporaryDirectory(prefix=".integration-", dir=ROOT) as temporary:
        small = json.loads(run([sys.executable, "scripts/verify_star_lift.py",
                               "--output", str(Path(temporary) / "small.json")]))
        hansen = json.loads(run([sys.executable, "scripts/verify_hansen_lift.py",
                                "--output", str(Path(temporary) / "hansen.json")]))
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
        "hansen_checks": hansen,
        "claim_boundary": {
            "local_ell_12509_bounds": [14, 17],
            "scholz_rhs_interval_from_local_bounds": [12522, 12525],
            "checked_mersenne_witness_additions": hansen["published_examples"][0]["additions"],
            "target_if_ell_12509_equals_17": 12525,
            "optimality_proved": False, "scholz_at_12509_proved": False,
            "whole_star_lift_formalised": False,
            "note": "Bounds 14 and 17 refer to the audited Lean theorems. The checked "
                    "12525-step witness still needs ell(12509)>=17, "
                    "or another argument linking its length to ell(12509)."},
        "runtime_seconds": round(time.perf_counter() - started, 6)}
    with args.output.open("x") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"report": str(args.output), "audited_theorems": audited,
                      "runtime_seconds": report["runtime_seconds"]}))


if __name__ == "__main__":
    main()
