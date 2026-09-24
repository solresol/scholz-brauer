#!/usr/bin/env python3
"""Cross-check exclusion certificates, corruptions, budgets and saved 12509 DAG."""
import argparse
import copy
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

from check_12509 import check_chain
from check_exclusion import check_exclusion
from exclusion_certificate import generate
from verify_hansen_lift import addition_prefixes

ROOT = Path(__file__).resolve().parents[1]
SAVED = ROOT / "results/2026-09-25-12509-exclusion-certificate.json"


def main():
    if not __debug__:
        raise RuntimeError("verification requires assertions; do not use Python -O")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    started = time.perf_counter()
    now = datetime.now(ZoneInfo("Australia/Sydney"))
    inputs = [ROOT / "scripts" / name for name in
              ("verify_exclusion.py", "exclusion_certificate.py", "check_exclusion.py",
               "check_12509.py", "verify_hansen_lift.py")]
    inputs.append(SAVED)
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in inputs}
    prefixes = list(addition_prefixes(max_steps=8, max_endpoint=64))
    shortest = {}
    for chain in prefixes:
        shortest[chain[-1]] = min(shortest.get(chain[-1], 100), len(chain)-1)
    excluded = witnesses = 0
    for n in range(1, 65):
        for steps in range(9):
            result = generate(n, steps)
            if shortest.get(n, 100) <= steps:
                assert result["status"] == "witness" and result["certificate"] is None
                check_chain(result["witness"])
                assert result["witness"][-1] == n and len(result["witness"]) <= steps+1
                witnesses += 1
            else:
                assert result["status"] == "excluded" and result["witness"] is None
                checked = check_exclusion(result["certificate"], target=n, max_steps=steps)
                assert checked["checked_occurrences"] == result["visited"]
                excluded += 1

    negatives = []

    def reject(label, doc, target=7, steps=3, budget=2000000):
        try:
            check_exclusion(doc, target=target, max_steps=steps, visit_budget=budget)
        except (ValueError, TimeoutError) as error:
            negatives.append({"case": label, "error": str(error)})
        else:
            raise AssertionError(f"accepted {label}")

    good = generate(7, 3)["certificate"]
    for key, value in (("format", "v0"), ("target", 8), ("target", True),
                       ("max_steps", 4), ("max_steps", 3.0), ("root", -1),
                       ("root", True), ("root", 1000), ("nodes", [])):
        bad = copy.deepcopy(good)
        bad[key] = value
        reject(f"invalid {key}={value}", bad)
    bad = copy.deepcopy(good)
    bad["extra"] = 1
    reject("unexpected field", bad)
    for node in (["bound", 0], ["unknown"], ["split", None], [], ["gap", 0]):
        bad = copy.deepcopy(good)
        bad["nodes"][0] = node
        reject(f"invalid rule {node}", bad)
    for edge in ([2, good["root"]], [2, -1], [True, 0], [2, True], [2, 0, 0], [8, 0]):
        bad = copy.deepcopy(good)
        bad["nodes"][-1] = ["split", [edge]]
        reject(f"invalid edge {edge}", bad)
    bad = copy.deepcopy(good)
    bad["nodes"][-1][1] = []
    reject("omitted branch", bad)
    bad = copy.deepcopy(good)
    bad["nodes"][-1][1] *= 2
    reject("duplicated branch", bad)
    bad = copy.deepcopy(good)
    bad["nodes"].append(copy.deepcopy(bad["nodes"][-1]))
    bad["root"] += 1
    reject("unreachable node", bad)
    for rule, n, steps, label in (("bound", 7, 3, "false bound"),
                                  ("gap", 7, 3, "gap too early"),
                                  ("gap", 2, 1, "available target summands"),
                                  ("bound", 1, 0, "reached singleton target"),
                                  ("split", 2, 0, "split without remaining steps")):
        doc = {"format": good["format"], "target": n, "max_steps": steps,
               "root": 0, "nodes": [[rule, []] if rule == "split" else [rule]]}
        reject(label, doc, n, steps)
    reject("checker zero budget", good, budget=0)

    # A deliberately false proof shares a gap node between contexts. Its first
    # use is valid at [1,2,3,4,8]; a later use at [1,2,3,5,10] has 15=5+10.
    # A checker caching acceptance by node id would wrongly accept this object.
    nodes = [["gap"]]

    def bogus(chain, left):
        if left == 1:
            return 0
        choices = sorted({a+b for a in chain for b in chain
                          if chain[-1] < a+b <= 15 and (a+b)*2**(left-1) >= 15})
        edges = [[v, bogus(chain+[v], left-1)] for v in choices]
        nodes.append(["split", edges])
        return len(nodes)-1

    root = bogus([1], 5)
    reject("shared gap rechecked in each context",
           {"format": good["format"], "target": 15, "max_steps": 5,
            "root": root, "nodes": nodes}, 15, 5)
    assert negatives[-1]["error"] == "target has available summands"

    budget_cases = []
    total = generate(7, 3)["visited"]
    for budget in (0, 1, total-1, total):
        result = generate(7, 3, budget)
        assert result["status"] == ("excluded" if budget == total else "budget")
        assert (result["certificate"] is not None) == (budget == total)
        budget_cases.append({"budget": budget, "status": result["status"]})
    reject("checker just below sufficient budget", good, budget=total-1)
    assert check_exclusion(good, target=7, max_steps=3,
                           visit_budget=total)["checked_occurrences"] == total
    invalid_requests = [(0, 3, 10), (True, 3, 10), (2**30+1, 3, 10),
                        (7, -1, 10), (7, 33, 10), (7, 3, -1), (7, 3, True)]
    for request in invalid_requests:
        try:
            generate(*request)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted invalid generator request {request}")

    commands = []
    with tempfile.TemporaryDirectory(prefix=".exclusion-", dir=ROOT) as directory:
        output = Path(directory) / "proof.json"

        def run(argv, expected=0):
            proc = subprocess.run(argv, cwd=ROOT, text=True, capture_output=True, timeout=10)
            assert (proc.returncode == 0) == (expected == 0)
            commands.append({"argv": argv, "exit_code": proc.returncode,
                             "stdout": proc.stdout, "stderr": proc.stderr})
            return proc

        base = [sys.executable, "scripts/exclusion_certificate.py"]
        run(base + ["7", "3", "--node-budget", "0", "--output", str(output)])
        assert not output.exists()
        run(base + ["7", "4", "--output", str(output)])
        assert not output.exists()
        run(base + ["7", "3", "--output", str(output)])
        before = output.read_bytes()
        run(base + ["7", "3", "--output", str(output)], expected=1)
        assert output.read_bytes() == before
        run([sys.executable, "-O", "scripts/check_exclusion.py", str(output),
             "--target", "7", "--max-steps", "3"])
        output.write_text(json.dumps({**good, "nodes": [["bound"]], "root": 0}))
        run([sys.executable, "-O", "scripts/check_exclusion.py", str(output),
             "--target", "7", "--max-steps", "3"], expected=1)

    saved = json.loads(SAVED.read_text())
    regenerated = None
    if args.regenerate:
        regenerated = generate(12509, 16)
        assert regenerated.pop("certificate") == saved
    research = check_exclusion(saved, target=12509, max_steps=16)
    assert research["checked_occurrences"] == 1345873
    assert all(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest
               for name, digest in hashes.items())
    report = {"started_at_australia_sydney": now.isoformat(),
              "weekday_australia_sydney": now.strftime("%A"),
              "python": platform.python_version(), "dependencies": "Python standard library",
              "seed": None, "input_sha256": hashes,
              "oracle": {"max_steps": 8, "max_endpoint": 64, "prefixes": len(prefixes)},
              "small_exclusions": excluded, "small_witnesses": witnesses,
              "negative_cases": negatives, "budget_cases": budget_cases,
              "invalid_generator_requests": len(invalid_requests),
              "commands": commands, "regenerated_12509": regenerated,
              "saved_12509": research, "certificate_bytes": SAVED.stat().st_size,
              "runtime_seconds": round(time.perf_counter()-started, 6)}
    with args.output.open("x") as out:
        out.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"report": str(args.output), "small_exclusions": excluded,
                      "small_witnesses": witnesses, "negative_cases": len(negatives),
                      "saved_12509": research, "runtime_seconds": report["runtime_seconds"]}))


if __name__ == "__main__":
    main()
