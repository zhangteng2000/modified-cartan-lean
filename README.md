# Modified Cartan - Lean 4 + mathlib

This repository formalizes *The modified Cartan conjecture* by Alexandre Eremenko, Zongben Xu, and Teng Zhang.

**[Read the paper: Modified Cartan conjecture (PDF)](Modified%20Cartan%20conjecture.pdf)**

All 19 labeled results have complete Lean proofs. The formalization also covers the C-class definition, the exact optimal radius **R₅ = 2 - √3**, the full Gaussian counterexample, the sharp diameter obstructions, and the geometric applications to algebraic tori and projective space. The proofs preserve the paper's constants, recursive radii, arbitrary open sets, non-strict diameter endpoint, and two-way equivalences.

## Verification status

- **289 local Lean modules** rebuilt successfully.
- **1,020 theorem declarations** checked by the recursive axiom audit.
- **54 manuscript proof entry points** checked, together with typed examples of the target propositions.
- **No `sorry`, `admit`, or manuscript-specific axioms.** The only permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The project pins Lean to **v4.34.0-rc1** and mathlib to commit `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

## Documentation

- [Final verification report](docs/FINAL_REPORT.md): manuscript results, proof names, source locations, constants, and axiom dependencies.
- [Formalization coverage](FORMALIZATION_STATUS.md) and the [machine-readable proof correspondence](verification/manuscript-coverage.json).
- [Build and audit results](verification/result.json) and the [complete theorem axiom inventory](verification/axiom-summary.json).
- [Proof dependency diagram](docs/DEPENDENCIES.md) and the [full compiler dependency inventory](verification/dependencies.json).
- [Geometric model](docs/GEOMETRIC_MODEL.md), [classical Cartan extraction](docs/CARTAN_EXTRACTION.md), and [manuscript correspondence](docs/MANUSCRIPT_CORRESPONDENCE.md).
- [PDF compilation record and statement index](verification/manuscript-pdf.json): manuscript hash, result numbers, and PDF pages.

## Reproduce the proofs

After installing elan, run these commands from the repository root:

```text
lake exe cache get
lake build
lake env lean ManuscriptCheck.lean
lake env lean Audit.lean
```

The toolchain and dependency versions are fixed by the files in this repository.

## Full verification on Windows

After obtaining the dependency cache, run in PowerShell 7:

```powershell
.\verify.ps1 -PackageRoot (Resolve-Path '.lake/packages').Path -Fresh
```

The script checks the PDF hash and compiled statement index, the correspondence of all 19 manuscript results, the proof entry points, and the pinned dependency revisions and clean worktrees. It rebuilds every local Lean module in a fresh temporary directory, runs the full `lake build`, and then checks `ManuscriptCheck.lean` and `Audit.lean`.

At most four ready modules are compiled in each batch. The dependency packages' compiled cache can be reused; local proof modules are rebuilt from source when `-Fresh` is supplied. Use `-PackageRoot` with an absolute path to another cache of the same pinned dependencies if needed. The script prints its verification directory, which contains the logs and hashes. The delivered verification records are also available in [`verification/`](verification/).
