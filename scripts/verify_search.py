#!/usr/bin/env python3
"""Compile and cross-check the exact search; optionally exclude <=16 for 12509.

The independent Python traversal uses sets of all ordered pair sums and a
one-step complement test. Neither traversal imports a table of minimum lengths.
Reports are computational evidence, not Lean proofs or portable proof objects.
"""
import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import tempfile
import time
from zoneinfo import ZoneInfo

from check_12509 import check_chain
from check_certificate import check_document
from verify_hansen_lift import addition_prefixes

ROOT = Path(__file__).resolve().parents[1]


def python_search(target, steps, budget=2000000):
    """Independent recursive decision procedure, with explicit incomplete status."""
    visits = 0

    def visit(chain):
        nonlocal visits
        if visits == budget:
            raise TimeoutError("Python node budget reached; no exclusion established")
        visits += 1
        if chain[-1] == target:
            return chain
        left = steps + 1 - len(chain)
        if left == 0 or chain[-1] * 2**left < target:
            return None
        earlier = set(chain)
        if left == 1:
            return chain + [target] if any(target-a in earlier for a in chain) else None
        lower = (target + 2**(left-1) - 1) // 2**(left-1)
        candidates = {a+b for a in chain for b in chain}
        for value in sorted(candidates):
            if chain[-1] < value <= target and value >= lower:
                found = visit(chain + [value])
                if found is not None:
                    return found
        return None

    started = time.perf_counter()
    try:
        witness = visit([1])
        status = "exhausted" if witness is None else "witness"
    except TimeoutError:
        witness, status = None, "budget"
    return {"target": target, "max_steps": steps, "node_budget": budget,
            "status": status, "witness": witness, "visited": visits,
            "runtime_seconds": round(time.perf_counter()-started, 6)}


def main():
    if not __debug__:
        raise RuntimeError("verification requires assertions; do not use Python -O")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--research", action="store_true", help="also run both 12509 exclusions")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    started = time.perf_counter()
    now = datetime.now(ZoneInfo("Australia/Sydney"))
    inputs = [ROOT / "scripts" / name for name in
              ("search_chain.cpp", "verify_search.py", "check_12509.py",
               "check_certificate.py", "verify_hansen_lift.py")]
    inputs += [ROOT / "data/12509-hansen.json",
               ROOT / "results/2026-09-21-12509-hansen-certificate.json"]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in inputs}
    commands = []

    def run(argv, timeout=180):
        begin = time.perf_counter()
        result = subprocess.run(argv, cwd=ROOT, text=True, capture_output=True,
                                timeout=timeout, check=True)
        commands.append({"argv": argv, "exit_code": result.returncode,
                         "runtime_seconds": round(time.perf_counter()-begin, 6),
                         "stdout": result.stdout, "stderr": result.stderr})
        return result.stdout

    with tempfile.TemporaryDirectory(prefix=".search-", dir=ROOT) as directory:
        binary = str(Path(directory) / "search_chain")
        compiler = run(["c++", "--version"])
        run(["c++", "-std=c++17", "-O3", "-Wall", "-Wextra", "-Werror",
             "scripts/search_chain.cpp", "-o", binary])

        def search(n, steps, budget=2000000, prefix=()):
            argv = [binary, str(n), str(steps), str(budget)] + list(map(str, prefix))
            result = json.loads(run(argv))
            if result["witness"]:
                check_chain(result["witness"])
                assert result["witness"][-1] == n and len(result["witness"]) <= steps+1
            return result

        # Completely unpruned Python enumeration is independent of both searches.
        prefixes = list(addition_prefixes(max_steps=8, max_endpoint=64))
        shortest = {}
        for chain in prefixes:
            shortest[chain[-1]] = min(shortest.get(chain[-1], 100), len(chain)-1)
        comparisons = 0
        for n in range(1, 65):
            for steps in range(9):
                expected = shortest.get(n, 100) <= steps
                cpp = search(n, steps)
                py = python_search(n, steps)
                assert cpp["status"] == py["status"] == ("witness" if expected else "exhausted")
                comparisons += 1

        # A budget stop must preserve every possible solution in disjoint pending
        # subtrees. Compare full oracle solutions, then restart every saved prefix.
        solutions = [c for c in prefixes if c[-1] == 29 and len(c) <= 8]
        assert len(solutions) == 132
        checkpoint_cases = []
        for budget in (0, 1, 2, 4, 7):
            partial = search(29, 7, budget)
            assert partial["status"] == "budget"
            pending = partial["pending_prefixes"]
            for i, p in enumerate(pending):
                check_chain(p)
                assert not any(p[:len(q)] == q or q[:len(p)] == p
                               for q in pending[i+1:])
            assert all(sum(c[:len(p)] == p for p in pending) == 1 for c in solutions)
            for p in pending:
                expected = any(c[:len(p)] == p for c in solutions)
                assert search(29, 7, prefix=p)["status"] == ("witness" if expected else "exhausted")
            checkpoint_cases.append({"budget": budget, "pending_count": len(pending)})
        # Exactly sufficient budget may still finish; zero budget cannot exclude.
        assert search(1, 0, 0)["status"] == "budget"
        assert search(1, 0, 1)["status"] == "witness"
        assert search(3, 1, 1)["status"] == "exhausted"
        assert python_search(29, 7, 0)["status"] == "budget"
        negatives = [["0", "1", "10"], ["2", "33", "10"],
                     ["1073741825", "1", "10"], ["2", "1", "-1"],
                     ["2x", "1", "10"], ["2", "1", "10", "2"],
                     ["5", "3", "10", "1", "2", "5"],
                     ["4", "2", "10", "1", "2", "2"],
                     ["2", "1", "10", "1", "2", "4"],
                     ["3", "2", "10", "1", "2", "4"]]
        for bad in negatives:
            result = subprocess.run([binary] + bad, capture_output=True, text=True, timeout=5)
            assert result.returncode == 2 and not result.stdout

        fixture = json.loads((ROOT / "data/12509-hansen.json").read_text())
        # Require an actually non-star witness with the non-star step inside
        # the searched suffix, guarding against accidental star-only generation.
        nonstar = search(12509, 17, prefix=fixture["chain"][:6])
        assert nonstar["status"] == "witness"
        assert any(nonstar["witness"][i]-nonstar["witness"][i-1]
                   not in nonstar["witness"][:i] for i in range(1, 18))

        research = None
        if args.research:
            cpp = search(12509, 16, 10000000)
            py = python_search(12509, 16)
            assert cpp["status"] == py["status"] == "exhausted"
            assert not cpp["pending_prefixes"]
            check_chain(fixture["chain"])
            assert len(fixture["chain"]) == 18 and fixture["chain"][-1] == 12509
            saved = json.loads((ROOT / "results/2026-09-21-12509-hansen-certificate.json").read_text())
            check_document(saved, exponent=12509, additions=12525)
            research = {"cpp": cpp, "python": py, "ell_12509": 17,
                        "mersenne_witness_additions": 12525,
                        "scholz_at_12509_computationally_established": True,
                        "lean_optimality_or_scholz_proof": False}

    assert all(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest
               for name, digest in hashes.items())
    report = {"started_at_australia_sydney": now.isoformat(),
              "weekday_australia_sydney": now.strftime("%A"),
              "python": platform.python_version(), "compiler": compiler.strip(),
              "dependencies": "Python standard library and C++17 standard library",
              "seed": None, "input_sha256": hashes, "commands": commands,
              "oracle": {"max_steps": 8, "max_endpoint": 64, "prefixes": len(prefixes)},
              "small_decision_comparisons": comparisons,
              "checkpoint_cases": checkpoint_cases, "negative_checks": len(negatives),
              "nonstar_suffix_search": nonstar, "research": research,
              "runtime_seconds": round(time.perf_counter()-started, 6)}
    with args.output.open("x") as out:
        out.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"report": str(args.output), "runtime_seconds": report["runtime_seconds"],
                      "research": research}, indent=2))


if __name__ == "__main__":
    main()
