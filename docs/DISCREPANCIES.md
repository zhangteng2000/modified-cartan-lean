# Manuscript-to-code discrepancies

## D1 — Explicit absorption radii (RESOLVED)

The earlier `AbsorptionTheorem` definition only asserts existence of some positive radius. The manuscript specifies `r₁ = 1`, `r₂ = 2 - √3`, and `rₘ = rₘ₋₁ / (1024 (Kₘ + m))`. The existential statement is not an adequate final target. `ExplicitAbsorptionTheorem` in `AnalyticStatements.lean` now uses the exact recursion and includes the obligation to produce valid exponents for the Wronskian estimate at a = 1/4, b = 1/2. Both `explicitAbsorptionTheorem_proved` and the weaker corollary `absorptionTheorem_proved` now have complete proofs. The actual exponent sequence and the exact recursive radii are included.

## D2 — Geometric model (RESOLVED)

`manifoldKobayashiRoyden` now uses actual mathlib manifold differentials and tangent fibers. `manifold_metric_eq_coordinate_metric` proves equality with the coordinate disk infimum for a complex embedded manifold. Both disk translations and injectivity of the embedding differential are proved. The intrinsic torus statements, closedness, compact lower bound and exact polynomial zero-locus identification have passed the full audit. The finite Laurent presentation and embedded complex manifold data encode the manuscript smooth closed subvariety hypothesis; see GEOMETRIC_MODEL.md.

## D3 — Connectedness (CHECKED in current definitions)

`IsCClass`, `CPartition`, `SharpFiveTheorem`, and `SharpTwoAbsorption` do not assume connectedness. Connectedness may be used only where the manuscript uses it, such as the auxiliary result about two dominant indices after extraction. Endpoint diameter is `≤ log 3`, not a strict bound.

Revision 2026-09-19: `def:cclass` now says “region”, whereas the unchanged
`thm:sharp-five` still allows arbitrary nonempty open sets. The more general Lean
predicate is retained and applies in particular to regions. No connectedness
assumption is added to a theorem. The two-dominant-index discussion was removed
from the manuscript and its existing Lean proof is now solely an auxiliary
result. See `REVISION_2026-09-19.md`.

## D4 — Status accounting (CORRECTED)

The current theorem count includes auxiliary facts. `lem:growth`, `lem:envelope`, `lem:two-point-kernel`, and `lem:poisson-mean` now have complete proofs. Proposition definitions, one-direction implications, special cases, and algebraic ingredients are not counted as complete manuscript results.

D1 update: the exact recursive absorption radii are now proved, including r₂ = 2−√3 and ηₘ = 1/[1024(Kₘ+m)]. The explicit theorem produces valid exponents; no unspecified radius replaces the manuscript formula.

## D5 — Scope of the classical input (CHECKED)

The manuscript cites the historical arbitrary-p Cartan theorem in its introduction. Its sharp-five proof needs only p = 5. In accordance with the execution requirement to prove the precise classical theorem required by the paper, CartanExtractionAt 5 is proved, with p = 3 and p = 4 as supporting instances. The unused general all-p proposition target was removed during cleanup. No principal manuscript statement was weakened, and no all-p extraction theorem or Yamanoi theorem is claimed or assumed. The revised Yamanoi paragraph remains bibliographic background.

## Final correspondence review

The revised paper has 19 labeled theorem/lemma/proposition/corollary environments plus def:cclass. Every one is mapped to its actual Lean proof or definitions in ../verification/manuscript-coverage.json. The complete Gaussian construction, exact optimal radius, disk diameter formula, both diameter obstructions and projective tangent dimension bound are mapped as well. All mathematical discrepancies affecting those results have been resolved; D3 records the retained terminology distinction.
