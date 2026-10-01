#!/usr/bin/env python3
"""Bounded kernel-evaluation probe of the existing 12509 exclusion DAG.

This only transports the saved syntax into Lean. The generated theorem uses
kernel `decide`, never native_decide. A failed or timed-out probe proves nothing.
Run after `cd lean && lake build`; the temporary source is removed on exit.
"""
import argparse
import hashlib
import json
import os
import signal
from pathlib import Path
import subprocess
import tempfile
import time
from datetime import datetime
from zoneinfo import ZoneInfo

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results/2026-09-25-12509-exclusion-certificate.json"
EXPECTED = "516a54800a296da300cc15da318c40b06b08a18270c93b8467f3f843a8b074e9"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--data-only", action="store_true", help="isolate declaration elaboration from kernel checking")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if not 1 <= args.timeout <= 300:
        raise ValueError("timeout must be in 1..300 seconds")
    raw = SOURCE.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED:
        raise ValueError("saved independently checked certificate hash changed")
    document = json.loads(raw)
    nodes = document["nodes"]
    lines = ["import ScholzBrauer.Exclusion", "namespace ScholzBrauer",
             "set_option maxRecDepth 65536", "set_option maxHeartbeats 2000000"]
    chunks = []
    for offset in range(0, len(nodes), 128):
        name = f"probeChunk{offset // 128}"
        chunks.append(name)
        literals = []
        for node in nodes[offset:offset + 128]:
            if node[0] in ("bound", "gap"):
                literals.append("." + node[0])
            else:
                literals.append(".split [" + ",".join(
                    f"({value},{child})" for value, child in node[1]) + "]")
        lines.append(f"def {name} : Array ExclusionNode := #[" + ",\n".join(literals) + "]")
    lines += ["def probeNodes : Array ExclusionNode := " + " ++ ".join(chunks)]
    if not args.data_only:
        lines += [f"theorem probe12509 : checkExclusion probeNodes 12509 [1] 1 16 {document['root']} = true := by decide",
                  "#print axioms probe12509"]
    lines.append("end ScholzBrauer")
    source = "\n".join(lines) + "\n"
    report = {"started": datetime.now(ZoneInfo("Australia/Sydney")).isoformat(),
              "certificate_sha256": digest, "target": 12509, "max_steps": 16,
              "distinct_nodes": len(nodes), "chunks": len(chunks),
              "generated_source_sha256": hashlib.sha256(source.encode()).hexdigest(),
              "generated_source_bytes": len(source.encode()),
              "timeout_seconds": args.timeout, "memory_limit_mb": 2048,
              "phase": "data_only" if args.data_only else "full",
              "seed": None, "method": "Lean kernel decide; no native_decide"}
    with tempfile.TemporaryDirectory(prefix="exclusion-probe-", dir=ROOT / ".git") as directory:
        path = Path(directory) / "Probe.lean"
        path.write_text(source)
        command = ["lake", "env", "lean", "-j", "1", "-M", "2048", str(path)]
        report["command"] = command
        report["cwd"] = str(ROOT / "lean")
        begin = time.perf_counter()
        process = subprocess.Popen(command, cwd=ROOT / "lean", text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            output, _ = process.communicate(timeout=args.timeout)
            report.update(exit_code=process.returncode, output=output,
                          status=("data_elaborated" if args.data_only else "kernel_checked")
                          if process.returncode == 0 else "failed")
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            output, _ = process.communicate()
            report.update(exit_code=process.returncode, output=output, status="timeout")
        report["runtime_seconds"] = round(time.perf_counter() - begin, 6)
    with args.output.open("x") as out:
        json.dump(report, out, indent=2)
        out.write("\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
