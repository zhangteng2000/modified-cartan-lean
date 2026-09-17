# Manuscript-to-code discrepancies

## D1 — Explicit absorption radii (OPEN)

The earlier `AbsorptionTheorem` definition only asserts existence of some positive radius. The manuscript specifies `r₁ = 1`, `r₂ = 2 - √3`, and `rₘ = rₘ₋₁ / (1024 (Kₘ + m))`. The existential statement is not an adequate final target. `absorptionRadius` already has this recursion, but its analytic applicability and linkage to the Wronskian exponents remain unproved. The final theorem must use the exact recursion; the existing existential form may remain as a corollary.

## D2 — Geometric model (OPEN)

The existing `kobayashiRoyden` definition uses coordinatewise holomorphic disks in a subset of a complex vector space. The project still needs to justify its agreement with the smooth algebraic variety/tangent-space formulation used in the manuscript before claiming the geometric results in full.

## D3 — Connectedness (CHECKED in current definitions)

`IsCClass`, `CPartition`, `SharpFiveTheorem`, and `SharpTwoAbsorption` do not assume connectedness. Connectedness may be used only where the manuscript uses it, such as the auxiliary result about two dominant indices after extraction. Endpoint diameter is `≤ log 3`, not a strict bound.

## D4 — Status accounting (CORRECTED)

The current theorem count includes auxiliary facts. `lem:growth`, `lem:envelope`, and `lem:two-point-kernel` now have complete proofs. Proposition definitions, one-direction implications, special cases, and algebraic ingredients are not counted as complete manuscript results.
