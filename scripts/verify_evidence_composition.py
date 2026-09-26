#!/usr/bin/env python3
"""Adversarial report-contract checks, not addition-chain proof checking.

Synthetic summaries isolate composition from the expensive searches. The full
integration separately replays real certificates and runs both exact searches.
unittest checks remain active under Python -O.
"""
import copy
import unittest

from verify_integration import compose_12509_evidence


def summaries():
    return {
        "witness": {"endpoint": 12509, "additions": 17},
        "mersenne": {"exponent": 12509, "additions": 12525,
                     "exact_endpoint_verified": True},
        "research": {
            "cpp": {"target": 12509, "max_steps": 16, "status": "exhausted",
                    "prefix": [1], "pending_prefixes": [], "witness": []},
            "python": {"target": 12509, "max_steps": 16,
                       "status": "exhausted", "witness": None}},
        "exclusion": {"target": 12509, "max_steps": 16, "status": "excluded"}}


class EvidenceComposition(unittest.TestCase):
    def test_matching_evidence(self):
        result = compose_12509_evidence(**summaries())
        self.assertEqual(result["computational_ell_12509_bounds"], [17, 17])
        self.assertEqual(result["scholz_rhs_from_computational_optimality"], 12525)
        self.assertEqual(result["checked_mersenne_witness_additions"], 12525)
        self.assertIs(result["scholz_at_12509_computationally_established"], True)

    def test_mismatched_or_incomplete_evidence(self):
        changes = [
            (("witness", "endpoint"), 12508),
            (("witness", "additions"), 18),
            (("witness", "additions"), 17.0),
            (("research",), None),
            (("research", "cpp", "target"), 12508),
            (("research", "python", "target"), 12508),
            (("research", "cpp", "max_steps"), 15),
            (("research", "python", "max_steps"), 15),
            (("research", "cpp", "status"), "budget"),
            (("research", "python", "status"), "budget"),
            (("research", "cpp", "status"), "witness"),
            (("research", "python", "status"), "witness"),
            (("research", "cpp", "prefix"), [1, 2]),
            (("research", "cpp", "prefix"), [True]),
            (("research", "cpp", "pending_prefixes"), [[1, 2]]),
            (("research", "cpp", "witness"), [1, 2]),
            (("research", "python", "witness"), [1, 2]),
            (("exclusion", "target"), 7),
            (("exclusion", "max_steps"), 15),
            (("exclusion", "status"), "budget"),
            (("mersenne", "exponent"), 12508),
            (("mersenne", "exact_endpoint_verified"), False),
            (("mersenne", "exact_endpoint_verified"), 1),
            # The valid star bound alone cannot close this numerical instance.
            (("mersenne", "additions"), 12526),
            (("mersenne", "additions"), -1),
            (("mersenne", "additions"), True),
        ]
        for path, value in changes:
            with self.subTest(path=path, value=value):
                records = copy.deepcopy(summaries())
                parent = records
                for key in path[:-1]:
                    parent = parent[key]
                parent[path[-1]] = value
                with self.assertRaises(ValueError):
                    compose_12509_evidence(**records)

    def test_missing_statement_fields(self):
        records = summaries()
        for name, record in records.items():
            if name == "research":
                continue
            for key in record:
                with self.subTest(record=name, key=key):
                    bad = copy.deepcopy(records)
                    del bad[name][key]
                    with self.assertRaises(ValueError):
                        compose_12509_evidence(**bad)


if __name__ == "__main__":
    unittest.main(verbosity=2)
