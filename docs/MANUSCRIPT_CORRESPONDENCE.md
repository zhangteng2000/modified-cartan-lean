# Manuscript correspondence

This document describes the correspondence between [paper.tex](../paper.tex) and the verified Lean statements. Every principal result has a complete proof.

## Explicit absorption radii

The manuscript specifies `r₁ = 1`, `r₂ = 2 - √3`, and `rₘ = rₘ₋₁ / (1024 (Kₘ + m))`. `ExplicitAbsorptionTheorem` in `AnalyticStatements.lean` uses this exact recursion and requires valid exponents for the Wronskian estimate at a = 1/4, b = 1/2. `explicitAbsorptionTheorem_proved` constructs these exponents and proves the stated radii. The existence-only statement `absorptionTheorem_proved` is a corollary.

## Geometric model

`manifoldKobayashiRoyden` uses actual mathlib manifold differentials and tangent fibers. `manifold_metric_eq_coordinate_metric` proves equality with the coordinate disk infimum for a complex embedded manifold. Disk translations and injectivity of the embedding differential are proved. The intrinsic torus statements, closedness, compact lower bound and exact polynomial zero-locus identification have passed the full audit. The finite Laurent presentation and embedded complex manifold data encode the manuscript's smooth closed subvariety hypothesis; see [GEOMETRIC_MODEL.md](GEOMETRIC_MODEL.md).

## C-classes and open sets

The manuscript defines C-classes on regions. The Lean predicates `IsCClass` and `CPartition` apply to arbitrary sets and hence also to regions. `SharpFiveTheorem` and `SharpTwoAbsorption` preserve the manuscript's arbitrary nonempty open-set hypotheses, including disconnected sets. Their endpoint diameter bound is `≤ log 3`.

## Result accounting

The manuscript has 19 labeled theorem, lemma, proposition and corollary environments, plus `def:cclass`. Each is mapped to its actual Lean proof or definition in [manuscript-coverage.json](../verification/manuscript-coverage.json). The complete Gaussian construction, exact optimal radius, disk diameter formula, both diameter obstructions and projective tangent dimension bound are mapped as well. The 1020 audited local theorem declarations include auxiliary facts; this count is distinct from the 19 principal manuscript results.

## Classical input

The sharp-five proof requires `CartanExtractionAt 5`, which is proved on the entire unit disk. The cases p = 3 and p = 4 are proved as supporting results. The arbitrary-p Cartan theorem and Yamanoi result cited in the introduction are bibliographic background; they are not used as axioms or claimed as separately formalized manuscript results. See [CARTAN_EXTRACTION.md](CARTAN_EXTRACTION.md).
