VERIFIED: All 19 principal labeled manuscript results, the C-class definition, the complete Gaussian counterexample, exact optimal five-function radius, sharp diameter obstructions and projective tangent dimension bound; 1020 local theorem declarations passed the full recursive axiom audit.
RELATIVE_VERIFIED: 0
WIP: 0
BLOCKED: 0
SORRY_COUNT: 0
USER_AXIOM_COUNT: 0

# Completed formalization

The manuscript is [Modified Cartan conjecture.pdf](../Modified%20Cartan%20conjecture.pdf), SHA-256 ca86a110643c3ba6502b7af2cd501c40414d1f0db6dead36d446223728f3e4eb. The compiled statement index and PDF provenance are recorded in [manuscript-pdf.json](../verification/manuscript-pdf.json). The 19 labeled results, one definition and supplemental conclusions are mapped in ../verification/manuscript-coverage.json. See ../FORMALIZATION_STATUS.md and FINAL_REPORT.md for exact theorem names and source locations.

## Final acceptance

- Fresh reconstruction of all 289 local Lean modules: passed.
- Complete lake build: passed, with no compilation errors.
- ManuscriptCheck.lean: 54 named proof entry points checked, plus typed examples for the proposition targets.
- Audit.lean: all 1020 theorem declarations audited; only propext, Classical.choice and Quot.sound occur.
- No local proof contains an unfinished placeholder, a manuscript-specific axiom, an opaque declaration, unsafe code or native_decide.
- Exact source hashes and full logs are in ../verification/.
- No principal result remains only as a Prop definition or under a missing mathematical assumption.

Verified at 2026-09-19T23:38:49.7170484Z. Build directory: C:/Users/HUAWEI/AppData/Local/Temp/ModifiedCartan-496d74ba5f6a402e9d378ff4c76a3a59.

## Mathematical closure

CartanCircle, QuantitativeWronskian and LogDerivativeEstimate prove the exact analytic toolbox. SharpTwoAbsorption closes the non-strict sharp two-term endpoint on arbitrary open sets. AbsorptionTheorem constructs valid Wronskian exponents and the exact recursive radii. QuotientStabilization and PartitionTheorem prove the main partition statement and its corollaries.

The final Cartan chain covers all finite quotient limits, the annular merging transfer, uniform triple anchors, the fourth-order endgame and common strict diagonal extraction on the entire unit disk. CartanFive proves the precise classical p = 5 input required by the manuscript. SharpFive proves the sharp five-function theorem and R5 = 2 - sqrt 3 using the already proved Gaussian construction.

The geometry uses the intrinsic manifold metric and actual tangent bundle. The null locus is identified with an explicit polynomial zero locus; compact complements have a positive lower bound. The projective equivalence, tangent union and dimension bound use the genuine projective quotient topology and manifold differentials.

## Reproducibility

The verified proof source checkpoint is e84e54567afaa9ded782f6d3da0826311407ac55. The project, manuscript and verification records are available at https://github.com/zhangteng2000/modified-cartan-lean.

Verification builds dependency-ready batches of at most 4 modules, then performs a normal full lake build. Fixed mathlib build artifacts are reused; every local module was rebuilt from source in a new directory. No mathematical or external blocker remains.
