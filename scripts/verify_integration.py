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
                       ROOT / "data/2026-10-01-hansen-lift-sources.json",
                       ROOT / "data/2026-10-04-source-recheck.json",
                       ROOT / "data/2026-10-05-source-recheck.json",
                       ROOT / "data/hansen-replay-fixtures.json",
                       ROOT / "data/2026-10-06-non-hansen29-source.json",
                       ROOT / "data/2026-10-08-clift109-source.json",
                       ROOT / "data/2026-10-08-clift109.png",
                       ROOT / "results/2026-09-30-29-hansen-allocation.json",
                       ROOT / "results/2026-09-30-12509-hansen-allocation.json",
                       ROOT / "results/2026-09-18-12509-star-certificate.json",
                       ROOT / "results/2026-09-21-12509-hansen-certificate.json",
                       ROOT / "results/2026-09-25-12509-exclusion-certificate.json",
                       ROOT / "results/2026-10-03-12509-limit15-exclusion.json"})
    hashes = {str(p.relative_to(ROOT)): sha256(p) for p in inputs}
    vendor = ROOT / "lean/vendor/formal-conjectures"
    provenance = json.loads((vendor / "provenance.json").read_text())
    for entry in provenance["files"]:
        if sha256(vendor / Path(entry["path"]).name) != entry["sha256"]:
            raise ValueError(f"vendored source hash mismatch: {entry['path']}")

    clift109 = json.loads(run([sys.executable, "scripts/experiment_clift109.py"]))
    one_gap_family = json.loads(run([sys.executable, "scripts/experiment_one_gap_family.py"]))
    non_hansen29 = json.loads(run([sys.executable, "scripts/experiment_non_hansen29.py"]))
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
        lower_fixture = Path(temporary) / "Exclusion12509Lower.lean"
        lean_lower = json.loads(run([sys.executable, "scripts/export_lean_exclusion.py",
                                    "--output", str(lower_fixture)]))
        if lower_fixture.read_bytes() != (ROOT / "lean/ScholzBrauer/Exclusion12509Lower.lean").read_bytes():
            raise ValueError("generated exclusion proof differs from compiled source")
        context_data = Path(temporary) / "Exclusion12509ContextsData.lean"
        context_proof = Path(temporary) / "Exclusion12509Optimal.lean"
        context_prefix = Path(temporary) / "Exclusion12509Partial.lean"
        context_parts = Path(temporary) / "context-parts"
        retained_parts = sorted((ROOT / "lean/ScholzBrauer").glob("Exclusion12509Part[0-9][0-9].lean"))
        if not retained_parts or [p.name for p in retained_parts] != [
                f"Exclusion12509Part{i:02d}.lean" for i in range(len(retained_parts))]:
            raise ValueError("retained context parts must be a nonempty initial segment")
        lean_contexts = json.loads(run([sys.executable, "scripts/export_lean_contexts.py",
                                       "--data-output", str(context_data),
                                       "--proof-output", str(context_proof),
                                       "--parts-output", str(context_parts),
                                       "--prefix-parts", str(len(retained_parts)),
                                       "--prefix-output", str(context_prefix)]))
        # The remaining generated parts and final theorem are candidates only.
        # Compare and subsequently compile/audit only the retained checkpoint.
        for generated in (context_data, context_prefix,
                          *(context_parts / p.name for p in retained_parts)):
            if generated.read_bytes() != (ROOT / "lean/ScholzBrauer" / generated.name).read_bytes():
                raise ValueError("generated context certificate differs from compiled source")
        bit_data = Path(temporary) / "Exclusion12509BitsData.lean"
        bit_proof = Path(temporary) / "Exclusion12509OptimalBits.lean"
        bit_parts = Path(temporary) / "bit-parts"
        lean_bits = json.loads(run([sys.executable, "scripts/export_lean_contexts.py",
                                   "--representation", "bits",
                                   "--data-output", str(bit_data),
                                   "--proof-output", str(bit_proof),
                                   "--parts-output", str(bit_parts)]))
        bit_files = {bit_data: "Exclusion12509BitsData.lean",
                     bit_proof: "Exclusion12509Optimal.lean"}
        bit_files.update({p: p.name for p in bit_parts.glob("*.lean")})
        if len(bit_files) != 14:
            raise ValueError("unexpected full bit-certificate file count")
        for generated, name in bit_files.items():
            if generated.read_bytes() != (ROOT / "lean/ScholzBrauer" / name).read_bytes():
                raise ValueError("generated bit certificate differs from compiled source")
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
        "non_hansen29_experiment": non_hansen29,
        "one_gap_family_experiment": one_gap_family,
        "clift109_experiment": clift109,
        "hansen_checks": hansen, "search_checks": search,
        "lean_export_checks": export,
        "hansen_allocation_checks": allocation,
        "exclusion_certificate_checks": exclusion,
        "lean_lower_bound_input_checks": lean_lower,
        "lean_context_input_checks": lean_contexts,
        "lean_bit_context_input_checks": lean_bits,
        "claim_boundary": {
            **computational,
            "lean_ell_12509_bounds": [17, 17],
            "target_if_ell_12509_equals_17": 12525,
            "optimality_or_scholz_at_12509_formalised": True,
            "context_enlargement_soundness_formalised": True,
            "kernel_checked_abstract_contexts": 29865,
            "total_abstract_contexts": 29865,
            "whole_star_lift_formalised": True,
            "lean_mersenne_12509_upper_bound": 12525,
            "hansen_lift_formalised": True,
            "lean_hansen_replay_fixture_exponents": [1, 29],
            "general_index_value_equivalence_formalised": False,
            "hansen_underlining_checker_formalised": True,
            "hansen_latest_marked_anchor_formalised": True,
            "hansen_shift_maximum_and_telescope_formalised": True,
            "positive_shifted_mersenne_injectivity_formalised": True,
            "hansen_sorted_replay_formalised": True,
            "labelled_hansen_allocation_independently_checked": True,
            "general_hansen_allocation_soundness_formalised": True,
            "lean_hansen_12509_shift_budget": 12525,
            "note": "Lean proves the general Hansen lift, the 12525 Mersenne bound, "
                    "the exact source length 17 and the numerical Scholz instance at 12509. "
                    "All 29865 abstract contexts are kernel checked with a proved bit-set "
                    "checker. The two independent exhaustive searches and portable checker "
                    "remain separate computational evidence. No Mersenne-chain optimum "
                    "or general Scholz theorem is claimed."},
        "runtime_seconds": round(time.perf_counter() - started, 6)}
    with args.output.open("x") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"report": str(args.output), "audited_theorems": audited,
                      "runtime_seconds": report["runtime_seconds"]}))


if __name__ == "__main__":
    main()
