#!/usr/bin/env python3
"""Independently check a labelled Hansen allocation and compile sorted replay.

No generator imports. Reconstruct caps from consecutive marked values, check
every source step, require the complete label family and its exact dependency
rules, then use integer arithmetic and the separate ordinary replay checker.
All bounds are checked before powers of two are allocated. Node order in the
JSON is immaterial and is not assumed to be a valid addition-chain order.
"""
import argparse
import hashlib
import json
from pathlib import Path

from check_certificate import check_document


def check_allocation(document, *, exponent, additions,
                     max_exponent=16384, max_nodes=20000):
    def require(condition, message):
        if not condition:
            raise ValueError(message)

    for limit in (max_exponent, max_nodes):
        require(type(limit) is int and limit > 0, "invalid budget")
    require(type(exponent) is int and 1 <= exponent <= max_exponent,
            "exponent outside budget")
    require(type(additions) is int and 0 <= additions < max_nodes,
            "addition count outside budget")
    require(isinstance(document, dict), "expected document object")
    require(document.get("format") == "hansen-labelled-allocation-v1", "unknown format")
    require(type(document.get("target_exponent")) is int
            and document["target_exponent"] == exponent, "target mismatch")
    require(type(document.get("additions")) is int
            and document["additions"] == additions, "addition declaration mismatch")
    source = document.get("source_chain")
    require(isinstance(source, list) and 1 <= len(source) <= max_nodes,
            "invalid source list")
    require(all(type(a) is int and 1 <= a <= exponent for a in source),
            "invalid source exponent")
    require(source[0] == 1 and source[-1] == exponent
            and all(a < b for a, b in zip(source, source[1:])), "invalid source order")
    require(additions == exponent + len(source) - 2, "incorrect Hansen count")
    marks = document.get("underlined_indices")
    require(isinstance(marks, list) and 1 <= len(marks) <= len(source), "invalid marks")
    require(all(type(i) is int and 0 <= i < len(source) for i in marks), "invalid mark index")
    require(marks[0] == 0 and marks[-1] == len(source) - 1
            and all(a < b for a, b in zip(marks, marks[1:])), "invalid mark order")

    # Different cap computation from the generator's maximum-demand update.
    caps = dict.fromkeys(source, 0)
    base_dependencies = {}
    for left, right in zip(marks, marks[1:]):
        anchor = source[left]
        caps[anchor] = source[right] - anchor
        for i in range(left + 1, right + 1):
            other = source[i] - anchor
            require(other in source[:i], "source step does not use latest mark")
            require(other <= caps[anchor], "requested summand exceeds shift cap")
            base_dependencies[source[i]] = ((anchor, other), (other, 0))
    supplied_caps = document.get("shift_caps")
    require(isinstance(supplied_caps, list) and len(supplied_caps) == len(source)
            and all(type(c) is int for c in supplied_caps)
            and supplied_caps == [caps[a] for a in source], "incorrect shift caps")
    require(sum(caps.values()) == exponent - 1, "shift count does not telescope")
    expected = {(a, k) for a in source for k in range(caps[a] + 1)}
    rows = document.get("nodes")
    require(isinstance(rows, list) and len(rows) == additions + 1 <= max_nodes,
            "incorrect node count")

    def label(raw):
        require(isinstance(raw, list) and len(raw) == 2
                and all(type(x) is int for x in raw), "invalid node label")
        result = tuple(raw)
        require(result in expected, "unallocated node label")
        return result

    dependencies = {}
    for row in rows:
        require(isinstance(row, dict), "invalid node row")
        node = label(row.get("label"))
        require(node not in dependencies, "duplicate node label")
        raw = row.get("summands")
        if node == (1, 0):
            require("summands" in row and raw is None, "seed has dependencies")
            dependencies[node] = None
            continue
        require(isinstance(raw, list) and len(raw) == 2, "missing two dependencies")
        pair = tuple(label(x) for x in raw)
        a, k = node
        rule = ((a, k - 1), (a, k - 1)) if k else base_dependencies[a]
        require(pair == rule, "incorrect labelled dependency rule")
        dependencies[node] = pair
    require(set(dependencies) == expected, "incomplete allocated family")
    require(all(a + k <= exponent for a, k in expected), "node exceeds endpoint envelope")
    values = {(a, k): ((1 << a) - 1) << k for a, k in expected}
    require(len(set(values.values())) == len(values), "node value collision")
    ordered = sorted(expected, key=values.__getitem__)
    require(ordered[0] == (1, 0) and ordered[-1] == (exponent, 0), "wrong endpoints")
    indices = {node: i for i, node in enumerate(ordered)}
    pairs = []
    for node in ordered[1:]:
        left, right = dependencies[node]
        require(left in dependencies and right in dependencies, "dependency closure failure")
        require(0 < values[left] < values[node] and 0 < values[right] < values[node]
                and values[left] + values[right] == values[node], "invalid integer sum")
        require(indices[left] < indices[node] and indices[right] < indices[node],
                "summands not earlier in sorted replay")
        pairs.append([indices[left], indices[right]])
    certificate = {"format": "addition-chain-indices-v1", "start": 1,
                   "target": {"kind": "mersenne", "exponent": exponent},
                   "additions": additions, "pairs": pairs}
    replay = check_document(certificate, exponent=exponent, additions=additions)
    require(replay == [values[node] for node in ordered], "ordinary replay differs")
    summary = {"exponent": exponent, "source_steps": len(source) - 1,
               "nodes": len(expected), "doubling_nodes": sum(caps.values()),
               "base_sum_nodes": len(source) - 1, "additions": additions,
               "dependency_edges_with_multiplicity": 2 * additions,
               "closure_count_endpoint_checked": True, "ordinary_replay_checked": True,
               "label_order_is_numeric_order": sorted(expected) == ordered,
               "general_allocation_soundness_formalised": False,
               "source_optimality_checked": False, "mersenne_optimality_checked": False}
    return summary, certificate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("allocation", type=Path)
    parser.add_argument("--exponent", type=int, required=True)
    parser.add_argument("--additions", type=int, required=True)
    parser.add_argument("--max-exponent", type=int, default=16384)
    parser.add_argument("--max-nodes", type=int, default=20000)
    args = parser.parse_args()
    if args.allocation.stat().st_size > 4_000_000:
        raise ValueError("input exceeds byte budget")
    raw = args.allocation.read_bytes()
    summary, _ = check_allocation(json.loads(raw), exponent=args.exponent,
                                 additions=args.additions, max_exponent=args.max_exponent,
                                 max_nodes=args.max_nodes)
    print(json.dumps(dict(summary, allocation_sha256=hashlib.sha256(raw).hexdigest()), indent=2))


if __name__ == "__main__":
    main()
