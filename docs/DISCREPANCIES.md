# Manuscript-to-code discrepancies

## D1 — Explicit absorption radii (RESOLVED)

The earlier `AbsorptionTheorem` definition only asserts existence of some positive radius. The manuscript specifies `r₁ = 1`, `r₂ = 2 - √3`, and `rₘ = rₘ₋₁ / (1024 (Kₘ + m))`. The existential statement is not an adequate final target. `ExplicitAbsorptionTheorem` in `AnalyticStatements.lean` now uses the exact recursion and includes the obligation to produce valid exponents for the Wronskian estimate at a = 1/4, b = 1/2. Both `explicitAbsorptionTheorem_proved` and the weaker corollary `absorptionTheorem_proved` now have complete proofs. The actual exponent sequence and the exact recursive radii are included.

## D2 — Geometric model (OPEN)

The existing `kobayashiRoyden` definition uses coordinatewise holomorphic disks in a subset of a complex vector space. The project still needs to justify its agreement with the smooth algebraic variety/tangent-space formulation used in the manuscript before claiming the geometric results in full.

## D3 — Connectedness (CHECKED in current definitions)

`IsCClass`, `CPartition`, `SharpFiveTheorem`, and `SharpTwoAbsorption` do not assume connectedness. Connectedness may be used only where the manuscript uses it, such as the auxiliary result about two dominant indices after extraction. Endpoint diameter is `≤ log 3`, not a strict bound.

## D4 — Status accounting (CORRECTED)

The current theorem count includes auxiliary facts. `lem:growth`, `lem:envelope`, `lem:two-point-kernel`, and `lem:poisson-mean` now have complete proofs. Proposition definitions, one-direction implications, special cases, and algebraic ingredients are not counted as complete manuscript results.

D1 update: the exact recursive absorption radii are now proved, including r₂ = 2−√3 and ηₘ = 1/[1024(Kₘ+m)]. The explicit theorem produces valid exponents; no unspecified radius replaces the manuscript formula.
