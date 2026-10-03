#!/usr/bin/env python3
"""Compress the pinned 12509/16 exclusion into checked context supersets.

Every group is keyed by source node, remaining budget and endpoint. Its context
is the union of all actual prefixes. Cross-context sums add obligations; they
are never silently discarded. The emitted Lean local checks independently
verify coverage and each child inclusion, and still need kernel compilation.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import time

from check_exclusion import check_exclusion

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results/2026-09-25-12509-exclusion-certificate.json"
EXPECTED = "516a54800a296da300cc15da318c40b06b08a18270c93b8467f3f843a8b074e9"
TARGET = 12509
CHUNK = 32
BATCH_CHUNKS = 78
BUILD_LANES = 3


def compress(document):
    nodes = document["nodes"]
    contexts = defaultdict(set)
    occurrences = 0

    def walk(index, prefix, remaining):
        nonlocal occurrences
        occurrences += 1
        contexts[index, remaining, prefix[-1]].update(prefix)
        if nodes[index][0] == "split":
            for value, child in nodes[index][1]:
                walk(child, prefix + [value], remaining - 1)

    walk(document["root"], [1], 16)
    edges_by_context = {}
    extra_edges = []
    for (index, remaining, last), values in list(contexts.items()):
        if nodes[index][0] != "split":
            continue
        edges = {v: (j, remaining - 1, v) for v, j in nodes[index][1]}
        # This is bounded by the pinned certificate, not a new chain search.
        for a in sorted(values):
            for b in sorted(values):
                value = a + b
                if (last < value <= TARGET and TARGET <= value * 2 ** (remaining - 1)
                        and value not in edges):
                    if remaining != 2:
                        raise ValueError("new nonterminal cross-context obligation")
                    key = (-1, 1, value)
                    contexts[key].update(values | {value})
                    edges[value] = key
                    extra_edges.append([index, remaining, last, value])
        edges_by_context[index, remaining, last] = sorted(edges.items())

    keys = sorted(contexts, key=lambda k: (k[1], k[0], k[2]))
    identifiers = {key: i for i, key in enumerate(keys)}
    records = []
    for key in keys:
        index, remaining, last = key
        values = contexts[key]
        kind = "gap" if index == -1 else nodes[index][0]
        edges = edges_by_context.get(key, [])
        if last == TARGET or max(values) > last:
            raise ValueError("invalid endpoint envelope")
        if kind == "gap":
            if remaining != 1 or any(TARGET - a in values for a in values):
                raise ValueError("widened final gap is false")
        elif kind == "bound":
            if last * 2 ** remaining >= TARGET:
                raise ValueError("widened doubling bound is false")
        else:
            next_values = {v for v, _ in edges}
            if any(a + b not in next_values for a in values for b in values
                   if last < a + b <= TARGET and TARGET <= (a + b) * 2 ** (remaining - 1)):
                raise ValueError("incomplete widened coverage")
            for value, child in edges:
                if (child[1] != remaining - 1 or child[2] != value
                        or not values | {value} <= contexts[child]):
                    raise ValueError("invalid child context inclusion")
        records.append([sorted(values), last, remaining, kind,
                        [[v, identifiers[child]] for v, child in edges]])
    return records, identifiers[document["root"], 16, 1], occurrences, extra_edges


def render(records, root):
    count = (len(records) + CHUNK - 1) // CHUNK
    options = ["namespace ScholzBrauer", "set_option Elab.async false",
               "set_option maxRecDepth 65536", "set_option maxHeartbeats 2000000"]
    data = ["-- Generated context supersets; each local check must still pass the Lean kernel.",
            "import ScholzBrauer.ExclusionContext"] + options
    for offset in range(0, len(records), CHUNK):
        blob = json.dumps(json.dumps(records[offset:offset + CHUNK], separators=(",", ":")))
        data.append(f"noncomputable def contextChunk{offset // CHUNK} : ContextTree := "
                    f"exclusion_contexts% {offset} {blob}")

    def tree(lo, hi):
        if hi - lo == 1:
            return f"contextChunk{lo}"
        mid = (lo + hi) // 2
        return f"(.branch {mid * CHUNK} {tree(lo, mid)} {tree(mid, hi)})"

    def lookup(lo, hi):
        if hi - lo == 1:
            return f"contextChunk{lo}.lookup i"
        mid = (lo + hi) // 2
        return f"(if i < {mid * CHUNK} then {lookup(lo, mid)} else {lookup(mid, hi)})"

    data += ["noncomputable def contexts12509 : ContextTree := " + tree(0, count),
             "noncomputable def contexts12509Lookup (i : ℕ) : ExclusionContext := " + lookup(0, count),
             "end ScholzBrauer"]
    proof = ["-- Generated by scripts/export_lean_contexts.py; kernel-checked context supersets.",
             "import ScholzBrauer.Exclusion12509ContextsData",
             "import ScholzBrauer.Example12509"] + options
    for j in range(count):
        proof.append(f"private theorem contextChecked{j} : contextChunk{j}.all "
                     "(checkContext 12509 contexts12509Lookup) = true := by decide +kernel")

    def combine(lo, hi):
        if hi - lo == 1:
            return f"contextChecked{lo}"
        mid = (lo + hi) // 2
        return f"(ContextTree.all_branch {combine(lo, mid)} {combine(mid, hi)})"

    proof += ["theorem contexts12509_all_checked : contexts12509.all "
              "(checkContext 12509 contexts12509Lookup) = true := " + combine(0, count),
              '''theorem contexts12509_lookup_eq (i : ℕ) : contexts12509Lookup i = contexts12509.lookup i := by rfl

theorem contexts12509_checked (i : ℕ) : checkContext 12509 contexts12509Lookup (contexts12509Lookup i) = true := by
  rw [contexts12509_lookup_eq]
  exact ContextTree.all_lookup contexts12509_all_checked i

/-- Excludes every addition chain with at most sixteen additions. -/
theorem seventeen_le_length12509 : 17 ≤ additionChainLength 12509 := by
  have hne := additionChainSteps_nonempty (n := 12509) (r := 17)
    chain12509 chain12509_valid (by decide) (by decide)
  have hlo := checkContext_lower_bound (r := 16) (i := ''' + str(root) + ''')
    contexts12509_checked (by decide +kernel) (by decide +kernel) (by decide +kernel) hne
  omega

/-- The checked witness and exclusion establish the exact source optimum. -/
theorem length12509_eq_seventeen : additionChainLength 12509 = 17 :=
  Nat.le_antisymm length12509_le_seventeen seventeen_le_length12509

/-- The numerical Scholz instance; no Mersenne-chain optimality is asserted. -/
theorem scholz12509 : additionChainLength (2 ^ 12509 - 1) ≤
    12509 - 1 + additionChainLength 12509 := by
  rw [length12509_eq_seventeen]
  exact mersenne12509_length_le_12525

end ScholzBrauer
''']
    # Separate modules checkpoint kernel work; dependencies permit at most
    # BUILD_LANES proof batches at once, including on clean CI builds.
    proof_lines = proof[7:7 + count]
    parts = {}
    batch_count = (count + BATCH_CHUNKS - 1) // BATCH_CHUNKS
    for batch in range(batch_count):
        imports = ["import ScholzBrauer.Exclusion12509ContextsData"]
        if batch >= BUILD_LANES:
            imports.append(f"import ScholzBrauer.Exclusion12509Part{batch - BUILD_LANES:02d}")
        else:
            imports.append("import ScholzBrauer.Exclusion12509Lower")
        start = batch * BATCH_CHUNKS
        lines = ["-- Generated kernel-check batch; do not edit."] + imports + options
        lines += [line.removeprefix("private ")
                  for line in proof_lines[start:start + BATCH_CHUNKS]]
        lines.append("end ScholzBrauer")
        parts[f"Exclusion12509Part{batch:02d}.lean"] = "\n".join(lines) + "\n"
    final_imports = [f"import ScholzBrauer.Exclusion12509Part{b:02d}"
                     for b in range(max(0, batch_count - BUILD_LANES), batch_count)]
    final = [proof[0]] + final_imports + options + proof[7 + count:]
    return "\n".join(data) + "\n", "\n".join(final) + "\n", parts, count



def render_prefix(part_count, total_contexts):
    """Aggregate a selected initial range; compilation is still required."""
    batch_count = ((total_contexts + CHUNK - 1) // CHUNK + BATCH_CHUNKS - 1) // BATCH_CHUNKS
    if not 1 <= part_count <= batch_count:
        raise ValueError("invalid prefix part count")
    count = min(part_count * BATCH_CHUNKS, (total_contexts + CHUNK - 1) // CHUNK)

    def tree(lo, hi):
        if hi - lo == 1:
            return f"contextChunk{lo}"
        mid = (lo + hi) // 2
        return f"(.branch {mid * CHUNK} {tree(lo, mid)} {tree(mid, hi)})"

    def combine(lo, hi):
        if hi - lo == 1:
            return f"contextChecked{lo}"
        mid = (lo + hi) // 2
        return f"(ContextTree.all_branch {combine(lo, mid)} {combine(mid, hi)})"

    lines = ["-- Generated by scripts/export_lean_contexts.py; partial local acceptance only."]
    lines += [f"import ScholzBrauer.Exclusion12509Part{b:02d}"
              for b in range(max(0, part_count - BUILD_LANES), part_count)]
    lines += ["namespace ScholzBrauer", "set_option maxRecDepth 65536",
              "set_option maxHeartbeats 2000000",
              "noncomputable def contexts12509Prefix : ContextTree := " + tree(0, count),
              "/-- Checks only the stored prefix of local obligations. This does not",
              "assert acceptance of all contexts or exclusion from the root. -/",
              "theorem contexts12509_prefix_checked : contexts12509Prefix.all "
              "(checkContext 12509 contexts12509Lookup) = true := " + combine(0, count),
              "/-- Every gap context in the checked prefix excludes its target. No",
              "acceptance of the unverified remainder is used. -/",
              "theorem contexts12509_gap_excluded (i : ℕ)",
              "    (hgap : (contexts12509Prefix.lookup i).rule = .gap) :",
              "    ¬ ChainReach 12509 (contexts12509Prefix.lookup i).values",
              "      (contexts12509Prefix.lookup i).last (contexts12509Prefix.lookup i).remaining := by",
              "  have hcheck := ContextTree.all_lookup contexts12509_prefix_checked i",
              "  exact checkContext_sound (lookup := fun _ => contexts12509Prefix.lookup i)",
              "    (fun _ => by simpa only [checkContext, hgap] using hcheck) 0",
              "end ScholzBrauer"]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-output", type=Path, required=True)
    parser.add_argument("--proof-output", type=Path, required=True)
    parser.add_argument("--parts-output", type=Path, required=True)
    parser.add_argument("--prefix-parts", type=int)
    parser.add_argument("--prefix-output", type=Path)
    args = parser.parse_args()
    if (args.prefix_parts is None) != (args.prefix_output is None):
        raise ValueError("both prefix arguments are required together")
    if args.prefix_output is not None and args.prefix_output.exists():
        raise FileExistsError(args.prefix_output)
    if args.data_output.exists() or args.proof_output.exists() or args.parts_output.exists():
        raise FileExistsError("output already exists")
    if args.data_output.resolve() == args.proof_output.resolve():
        raise ValueError("data and proof outputs must differ")
    started = time.perf_counter()
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED:
        raise ValueError("saved exclusion certificate hash changed")
    document = json.loads(raw)
    checked = check_exclusion(document, target=TARGET, max_steps=16)
    records, root, occurrences, extras = compress(document)
    data, proof, parts, count = render(records, root)
    with args.data_output.open("x") as out:
        out.write(data)
    with args.proof_output.open("x") as out:
        out.write(proof)
    if args.prefix_output is not None:
        with args.prefix_output.open("x") as out:
            out.write(render_prefix(args.prefix_parts, len(records)))
    args.parts_output.mkdir()
    for name, source in parts.items():
        (args.parts_output / name).write_text(source)
    print(json.dumps({"source_sha256": EXPECTED, "seed": None,
                      "contexts": len(records), "source_occurrences": occurrences,
                      "extra_edges": extras, "proof_chunks": count,
                      "chunk_size": CHUNK, "root": root,
                      "candidate_batches": len(parts), "max_parallel_batches": BUILD_LANES,
                      "requested_prefix_parts": args.prefix_parts,
                      "independent_source_check": checked, "lean_proof": False,
                      "runtime_seconds": round(time.perf_counter() - started, 6)}, indent=2))


if __name__ == "__main__":
    main()
