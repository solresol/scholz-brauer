# Unfinished residue proof, preserved 1 November 2026

The adjacent `.lean.txt` file preserves the original untracked
`lean/ScholzBrauer/Clift109Residues.lean` byte for byte. It is deliberately
outside the compiled Lean library and is not a verified theorem artifact.

SHA-256: `a74de1f484a58bf04db3afb3bd6244c5f8e12b2adfcee03525cf1c71dd6602dd`.
The original source-access record remains at
`../../data/2026-10-28-residue-source-recheck.json`; it records historical
access, not a fresh source check.

The draft proposes residue fingerprints and a 27-value necessary domain for
the two halving steps. None of its declarations is claimed checked here.
On 1 November, from `lean/`, `/usr/bin/time -p lake env lean
ScholzBrauer/Clift109Residues.lean` produced no diagnostics before deliberate
termination after 117.47 seconds (exit 143; user 65.81s, system 11.50s).
This was an incomplete compilation, not a counterexample or a proved result.
The exact slow declaration was not isolated. No toolchain was installed.

Resume in the intended Cloud environment: restore a working copy under
`lean/ScholzBrauer/`, isolate the expensive obligation, and complete the
pinned build and axiom audit before importing or claiming these results.
Keep the original here until the replacement is verified. The full Clift109
interval classification and exclusion remain incomplete.

## Completed replacement — 2 November 2026

The user-authorized daily research run resumed locally in the specified
repository. `../../lean/ScholzBrauer/Clift109Residues.lean` now completes the
argument; the original bytes above remain untouched. Profiling found expensive
nested Finset insertion reduction. A list-backed Finset and separate Fin cases
resolved it; the completed theorem includes both finite domains and residue
fingerprints for every budget-108 labelling. See
`../../results/2026-11-02-residues-lean.md` for checks and remaining obligations.
The historical incomplete-check statements above describe the archived file.
