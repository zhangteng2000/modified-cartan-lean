# Final formalization verification report

All 19 labeled manuscript results have complete Lean proof terms, together with the exact optimal radius, the full Gaussian counterexample, sharp diameter obstructions, and the projective tangent-space dimension bound. All 289 local modules were rebuilt successfully, and all 1,020 local theorems passed the recursive axiom audit.

Proof verification completed at `2026-09-19T23:38:49.7170484Z`. The verified proof source checkpoint is `e84e54567afaa9ded782f6d3da0826311407ac55`. The evidence is available in [result.json](../verification/result.json), the [build log](../verification/build.log), the [manuscript entry-point checks](../verification/manuscript-check.log), and the [axiom log](../verification/axioms.log).

## Manuscript and scope

The manuscript is [Modified Cartan conjecture.pdf](../Modified%20Cartan%20conjecture.pdf), a 25-page PDF with SHA-256 `ca86a110643c3ba6502b7af2cd501c40414d1f0db6dead36d446223728f3e4eb`.

The PDF was compiled directly from the manuscript covered by the proof audit. The [compilation record](../verification/manuscript-pdf.json) binds the PDF to the source hash and records the number, page, and PDF destination of each labeled result and definition. The definitions and theorem types were checked against the manuscript; the compiled index provides navigation and artifact-integrity checks.

The table below covers the 19 labeled results. Definition 1.1 (`def:cclass`) corresponds to `IsDominant`, `IsCClass`, and `CPartition` in [Basic.lean](../ModifiedCartan/Basic.lean). The formalization retains actual bounded quotient functions, uniform convergence on compact sets, a fixed dominant index, and strictly increasing subsequences.

The classical Cartan input used by the paper is proved for p = 5 on the entire unit disk, with p = 3 and p = 4 as supporting results. The historical arbitrary-p theorem, Borel/Picard discussion, and Yamanoi result in the introduction are bibliographic background, not additional author results claimed here or axioms imported into the development.

## Principal results and axiom dependencies

Every listed declaration is an actual theorem proof term. The axiom column is taken from the recursive `#print axioms` output. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

| Manuscript result | Exact Lean name | Source and line | Axiom dependencies |
|---|---|---|---|
| `thm:main` (1.2; p. 2) | `ModifiedCartan.partitionTheorem_proved` | [ModifiedCartan/PartitionTheorem.lean:104](../ModifiedCartan/PartitionTheorem.lean#L104) | `[propext, Classical.choice, Quot.sound]` |
| `thm:main` (1.2; p. 2) | `ModifiedCartan.partition_at_recursive_radius` | [ModifiedCartan/PartitionTheorem.lean:10](../ModifiedCartan/PartitionTheorem.lean#L10) | `[propext, Classical.choice, Quot.sound]` |
| `thm:sharp-five` (1.3; p. 3) | `ModifiedCartan.sharpFiveTheorem_proved` | [ModifiedCartan/SharpFive.lean:12](../ModifiedCartan/SharpFive.lean#L12) | `[propext, Classical.choice, Quot.sound]` |
| `thm:torus-zero` (1.4; p. 3) | `ModifiedCartan.torus_manifold_metric_zero_iff` | [ModifiedCartan/TorusManifold.lean:30](../ModifiedCartan/TorusManifold.lean#L30) | `[propext, Classical.choice, Quot.sound]` |
| `lem:cartan-circle` (2.1; p. 5) | `ModifiedCartan.cartanCircleEstimate_proved` | [ModifiedCartan/CartanCircle.lean:123](../ModifiedCartan/CartanCircle.lean#L123) | `[propext, Classical.choice, Quot.sound]` |
| `prop:wronskian` (2.2; p. 6) | `ModifiedCartan.quantitativeWronskian_proved` | [ModifiedCartan/QuantitativeWronskian.lean:11](../ModifiedCartan/QuantitativeWronskian.lean#L11) | `[propext, Classical.choice, Quot.sound]` |
| `lem:logderivative` (2.3; p. 7) | `ModifiedCartan.logDerivativeEstimate_proved` | [ModifiedCartan/LogDerivativeEstimate.lean:95](../ModifiedCartan/LogDerivativeEstimate.lean#L95) | `[propext, Classical.choice, Quot.sound]` |
| `lem:growth` (2.4; p. 8) | `ModifiedCartan.growthLemma_proved` | [ModifiedCartan/Growth.lean:52](../ModifiedCartan/Growth.lean#L52) | `[propext, Classical.choice, Quot.sound]` |
| `lem:envelope` (2.5; p. 8) | `ModifiedCartan.envelope_lemma` | [ModifiedCartan/Envelope.lean:122](../ModifiedCartan/Envelope.lean#L122) | `[propext, Classical.choice, Quot.sound]` |
| `lem:poisson-mean` (2.6; p. 9) | `ModifiedCartan.poissonMeanEstimate_proved` | [ModifiedCartan/LogPoisson.lean:246](../ModifiedCartan/LogPoisson.lean#L246) | `[propext, Classical.choice, Quot.sound]` |
| `thm:absorption` (3.1; p. 9) | `ModifiedCartan.explicitAbsorptionTheorem_proved` | [ModifiedCartan/AbsorptionTheorem.lean:72](../ModifiedCartan/AbsorptionTheorem.lean#L72) | `[propext, Classical.choice, Quot.sound]` |
| `thm:absorption` (3.1; p. 9) | `ModifiedCartan.absorption_at_recursive_radius` | [ModifiedCartan/AbsorptionTheorem.lean:60](../ModifiedCartan/AbsorptionTheorem.lean#L60) | `[propext, Classical.choice, Quot.sound]` |
| `cor:rank-adaptive-absorption` (3.2; p. 13) | `ModifiedCartan.rank_adaptive_absorption` | [ModifiedCartan/RankAdaptiveAbsorption.lean:10](../ModifiedCartan/RankAdaptiveAbsorption.lean#L10) | `[propext, Classical.choice, Quot.sound]` |
| `lem:stabilization` (4.1; p. 13) | `ModifiedCartan.stabilization_lemma` | [ModifiedCartan/QuotientStabilization.lean:30](../ModifiedCartan/QuotientStabilization.lean#L30) | `[propext, Classical.choice, Quot.sound]` |
| `cor:centers` (4.2; p. 15) | `ModifiedCartan.partition_at_center` | [ModifiedCartan/PartitionCenters.lean:63](../ModifiedCartan/PartitionCenters.lean#L63) | `[propext, Classical.choice, Quot.sound]` |
| `lem:two-point-kernel` (5.1; p. 16) | `ModifiedCartan.two_point_harmonic` | [ModifiedCartan/HarmonicKernel.lean:89](../ModifiedCartan/HarmonicKernel.lean#L89) | `[propext, Classical.choice, Quot.sound]` |
| `cor:geodesic-comparison` (5.2; p. 16) | `ModifiedCartan.geodesic_harmonic_comparison` | [ModifiedCartan/GeodesicComparison.lean:11](../ModifiedCartan/GeodesicComparison.lean#L11) | `[propext, Classical.choice, Quot.sound]` |
| `prop:sharp-two-absorption` (5.3; p. 17) | `ModifiedCartan.sharpTwoAbsorption_proved` | [ModifiedCartan/SharpTwoAbsorption.lean:87](../ModifiedCartan/SharpTwoAbsorption.lean#L87) | `[propext, Classical.choice, Quot.sound]` |
| `prop:torus-null-set` (6.1; p. 22) | `ModifiedCartan.torus_manifold_nullDirections_isClosed` | [ModifiedCartan/TorusManifold.lean:40](../ModifiedCartan/TorusManifold.lean#L40) | `[propext, Classical.choice, Quot.sound]` |
| `prop:torus-null-set` (6.1; p. 22) | `ModifiedCartan.torus_manifold_compact_metric_lower` | [ModifiedCartan/TorusManifold.lean:59](../ModifiedCartan/TorusManifold.lean#L59) | `[propext, Classical.choice, Quot.sound]` |
| `prop:torus-null-set` (6.1; p. 22) | `ModifiedCartan.torus_manifold_compact_inf_pos` | [ModifiedCartan/TorusManifold.lean:84](../ModifiedCartan/TorusManifold.lean#L84) | `[propext, Classical.choice, Quot.sound]` |
| `prop:torus-null-set` (6.1; p. 22) | `ModifiedCartan.torus_manifold_null_image_eq_zeroLocus` | [ModifiedCartan/TorusTangentAlgebraic.lean:51](../ModifiedCartan/TorusTangentAlgebraic.lean#L51) | `[propext, Classical.choice, Quot.sound]` |
| `prop:projective-equivalence` (6.2; p. 23) | `ModifiedCartan.projective_equivalence` | [ModifiedCartan/ProjectiveEquivalence.lean:78](../ModifiedCartan/ProjectiveEquivalence.lean#L78) | `[propext, Classical.choice, Quot.sound]` |
| `cor:projective-zero-directions` (6.3; p. 23) | `ModifiedCartan.projective_zero_directions` | [ModifiedCartan/ProjectiveTori.lean:175](../ModifiedCartan/ProjectiveTori.lean#L175) | `[propext, Classical.choice, Quot.sound]` |
| `cor:projective-zero-directions` (6.3; p. 23) | `ModifiedCartan.projectiveTorusTangentSpace_finrank_le` | [ModifiedCartan/ProjectiveTori.lean:197](../ModifiedCartan/ProjectiveTori.lean#L197) | `[propext, Classical.choice, Quot.sound]` |

## Supplemental results and complete counterexample

The counterexample uses an actual complex square-root branch, a holomorphic Gaussian primitive, and five explicitly defined functions. The functions a and b are related by z ↦ -z, with the exact `3/(4n)` estimate. The obstruction covers every `2 - sqrt 3 < R ≤ 1` and every strictly increasing subsequence.

| Result group | Exact Lean name | Source and line | Axiom dependencies |
|---|---|---|---|
| `cartan-extraction-required-by-paper` | `ModifiedCartan.cartanExtraction_three` | [ModifiedCartan/CartanThree.lean:33](../ModifiedCartan/CartanThree.lean#L33) | `[propext, Classical.choice, Quot.sound]` |
| `cartan-extraction-required-by-paper` | `ModifiedCartan.cartanExtraction_four` | [ModifiedCartan/CartanFour.lean:10](../ModifiedCartan/CartanFour.lean#L10) | `[propext, Classical.choice, Quot.sound]` |
| `cartan-extraction-required-by-paper` | `ModifiedCartan.cartanExtraction_five` | [ModifiedCartan/CartanFive.lean:10](../ModifiedCartan/CartanFive.lean#L10) | `[propext, Classical.choice, Quot.sound]` |
| `optimal-five-radius` | `ModifiedCartan.optimalFiveRadius_proved` | [ModifiedCartan/SharpFive.lean:30](../ModifiedCartan/SharpFive.lean#L30) | `[propext, Classical.choice, Quot.sound]` |
| `optimal-five-radius` | `ModifiedCartan.partition_five_at_sharpRadius` | [ModifiedCartan/SharpFive.lean:19](../ModifiedCartan/SharpFive.lean#L19) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-holomorphic-branch` | `ModifiedCartan.fivePhi_differentiable` | [ModifiedCartan/FiveExampleFunctions.lean:34](../ModifiedCartan/FiveExampleFunctions.lean#L34) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-holomorphic-branch` | `ModifiedCartan.fiveL_differentiable` | [ModifiedCartan/FiveExampleFunctions.lean:52](../ModifiedCartan/FiveExampleFunctions.lean#L52) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-holomorphic-branch` | `ModifiedCartan.fivePhi_sq` | [ModifiedCartan/FiveExampleFunctions.lean:62](../ModifiedCartan/FiveExampleFunctions.lean#L62) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-majorants-and-sign` | `ModifiedCartan.five_majorant_positive_gap` | [ModifiedCartan/FiveMajorant.lean:51](../ModifiedCartan/FiveMajorant.lean#L51) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-majorants-and-sign` | `ModifiedCartan.fiveL_re_pos_right` | [ModifiedCartan/FiveMajorant.lean:28](../ModifiedCartan/FiveMajorant.lean#L28) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-majorants-and-sign` | `ModifiedCartan.fivePhi_re_nonpos_iff` | [ModifiedCartan/FivePhiSign.lean:56](../ModifiedCartan/FivePhiSign.lean#L56) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-majorants-and-sign` | `ModifiedCartan.fivePhi_re_nonneg_iff` | [ModifiedCartan/FivePhiSign.lean:62](../ModifiedCartan/FivePhiSign.lean#L62) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-integral-and-tail` | `ModifiedCartan.gaussianPrimitive_hasDerivAt` | [ModifiedCartan/GaussianPrimitive.lean:24](../ModifiedCartan/GaussianPrimitive.lean#L24) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-integral-and-tail` | `ModifiedCartan.gaussianTransition_left_bound` | [ModifiedCartan/GaussianContour.lean:100](../ModifiedCartan/GaussianContour.lean#L100) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-integral-and-tail` | `ModifiedCartan.gaussianTransition_right_bound` | [ModifiedCartan/GaussianContour.lean:122](../ModifiedCartan/GaussianContour.lean#L122) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-exact-ratio-estimate` | `ModifiedCartan.fivea_div_fiveA_bound` | [ModifiedCartan/FiveExampleBounds.lean:48](../ModifiedCartan/FiveExampleBounds.lean#L48) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-exact-ratio-estimate` | `ModifiedCartan.fivea_complement` | [ModifiedCartan/FiveExampleBounds.lean:69](../ModifiedCartan/FiveExampleBounds.lean#L69) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-five-units-and-zero-sum` | `ModifiedCartan.fiveCounterexample_units` | [ModifiedCartan/FiveCounterexample.lean:26](../ModifiedCartan/FiveCounterexample.lean#L26) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-five-units-and-zero-sum` | `ModifiedCartan.fiveCounterexample_zeroSum` | [ModifiedCartan/FiveCounterexample.lean:37](../ModifiedCartan/FiveCounterexample.lean#L37) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-growth-and-vanishing` | `ModifiedCartan.fiveCounterexample_grows_at_zero` | [ModifiedCartan/FiveCounterexample.lean:43](../ModifiedCartan/FiveCounterexample.lean#L43) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-growth-and-vanishing` | `ModifiedCartan.fiveA_vanishes_negative_point` | [ModifiedCartan/FiveExampleLimits.lean:32](../ModifiedCartan/FiveExampleLimits.lean#L32) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-growth-and-vanishing` | `ModifiedCartan.fivea_sub_fiveA_vanishes_negative_point` | [ModifiedCartan/FiveExampleLimits.lean:74](../ModifiedCartan/FiveExampleLimits.lean#L74) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-growth-and-vanishing` | `ModifiedCartan.fiveCounterexample_vanishing_points` | [ModifiedCartan/FiveCounterexample.lean:52](../ModifiedCartan/FiveCounterexample.lean#L52) | `[propext, Classical.choice, Quot.sound]` |
| `gaussian-no-partition-any-subsequence` | `ModifiedCartan.fiveCounterexample_no_partition` | [ModifiedCartan/FiveCounterexample.lean:71](../ModifiedCartan/FiveCounterexample.lean#L71) | `[propext, Classical.choice, Quot.sound]` |
| `disk-diameter-formula` | `ModifiedCartan.disk_hyperbolicDiameter_iff` | [ModifiedCartan/DiskDiameter.lean:81](../ModifiedCartan/DiskDiameter.lean#L81) | `[propext, Classical.choice, Quot.sound]` |
| `disk-diameter-formula` | `ModifiedCartan.sharpRadius_log_diameter` | [ModifiedCartan/Radii.lean:32](../ModifiedCartan/Radii.lean#L32) | `[propext, Classical.choice, Quot.sound]` |
| `disk-diameter-formula` | `ModifiedCartan.sharpRadius_hyperbolicDiameter` | [ModifiedCartan/AbsorptionTheorem.lean:45](../ModifiedCartan/AbsorptionTheorem.lean#L45) | `[propext, Classical.choice, Quot.sound]` |
| `sharp-diameter-obstructions` | `ModifiedCartan.five_partition_diameter_cannot_increase` | [ModifiedCartan/FiveOptimalityUpper.lean:35](../ModifiedCartan/FiveOptimalityUpper.lean#L35) | `[propext, Classical.choice, Quot.sound]` |
| `sharp-diameter-obstructions` | `ModifiedCartan.two_absorption_diameter_cannot_increase` | [ModifiedCartan/TwoAbsorptionCounterexample.lean:87](../ModifiedCartan/TwoAbsorptionCounterexample.lean#L87) | `[propext, Classical.choice, Quot.sound]` |

## Constants, hypotheses, and geometric correspondence

- The radii remain `r1 = 1`, `r2 = 2 - sqrt 3`, and `r_m = r_(m-1)/(1024*(K_m+m))`. Valid values of `K_m` are constructed from the proved Wronskian estimate.
- The proofs retain `epsilon_p = r_(p-1)^(p-1)`, the rank-adaptive radius `r_d`, the envelope constants 8 and 64, the Poisson coefficients q and `q² - 1`, and the geodesic comparison constant `2C0`.
- The five-function and two-term absorption theorems allow arbitrary nonempty open sets, including disconnected sets, at the endpoint `diameter ≤ log 3`.
- Projective equivalence is proved in both directions for `p ≥ 3` and `0 < R ≤ 1`, using the actual quotient topology, product uniform structure, and manifold holomorphic maps.
- Torus subvarieties are presented as closed zero loci of finitely many Laurent equations with an embedded complex manifold structure. Tangent vectors are manifold tangent vectors, and ambient coordinates come from the embedding differential. Equality of the intrinsic Kobayashi-Royden pseudometric and the coordinate-disk definition is proved. The algebraic null-direction result identifies the entire zero locus, including the converse construction; see the [geometric model](GEOMETRIC_MODEL.md).
- The pseudometric takes values in the nonnegative extended reals, with the usual positive-infinity value for an empty infimum.

## mathlib and external dependencies

The Lean toolchain is `leanprover/lean4:v4.34.0-rc1`. The following dependencies are pinned. Module counts refer to the compiler's full `.ilean` import closure, including tactic infrastructure.

| Package | Pinned commit | Modules in import closure |
|---|---|---|
| mathlib | `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` | 3302 |
| plausible | `38e9c3ce15cbb63c92e90bb9a92e4eb82131f669` | 13 |
| LeanSearchClient | `2bc7cf064315b26bc38dac2e9612fb581be9b75f` | 4 |
| importGraph | `978b7ec9fbbf9a535114f1de8fe5b3778b358870` | 10 |
| proofwidgets | `99e8adeea3c3cd86b6b79ba01a1383bf2d31d055` | 13 |
| aesop | `c1c4362a130f12e632d252180a6c2a31d8fd4726` | 132 |
| Qq | `3b55e9d00c6b0018e5d984eb011b6f93c09bd163` | 14 |
| batteries | `01bc479e7432594821ba3fb0ca465211941de86d` | 78 |
| Cli | `af8bc067a4cc6c6df472a68909a3f40b1c76c43e` | 0 |

The closure also contains 1,399 Lean/Std core modules. All 3,302 mathlib modules and every other external module are listed individually in the [dependency appendix](MATHLIB_DEPENDENCIES.md). The [machine-readable inventory](../verification/dependencies.json) records direct import edges, transitive imports, pinned versions, and local references to mathlib declarations. The [generator](../scripts/dependency-audit.mjs) reads compiler metadata from the successful build. Compiler imports and logical axiom dependencies are distinct; the latter are recorded in [axiom-summary.json](../verification/axiom-summary.json).

The development reuses Poisson representation, Cauchy estimates, analytic zeros and meromorphic functions, compactness and Arzela-Ascoli, determinants, Laurent and polynomial zero loci, manifolds, and projectivization. The Cartan extraction, quantitative estimates, intrinsic-metric bridge, and required projective constructions are proved locally. The [library audit](LIBRARY_AUDIT.md) records the relevant APIs and original Cartan references.

## Manuscript correspondence

The [correspondence notes](MANUSCRIPT_CORRESPONDENCE.md) explain the exact recursive radii, intrinsic geometric model, C-class definition and open-set theorems, result accounting, and classical Cartan input. Every principal result has a complete proof with the manuscript's constants, hypotheses, and conclusion.

## Build and reproduction

The delivered proof audit rebuilt all local modules in a fresh directory using batches of at most four ready modules, then ran `lake build`, `lake env lean ManuscriptCheck.lean`, and `lake env lean Audit.lean`. Dependency commits and clean worktrees were checked. Style-linter suggestions in the logs are not compilation errors.

After installing elan, run from the repository root:

```text
lake exe cache get
lake build
lake env lean ManuscriptCheck.lean
lake env lean Audit.lean
```

For the full verification script on Windows, use PowerShell 7:

```powershell
.\verify.ps1 -PackageRoot (Resolve-Path '.lake/packages').Path -Fresh
```

The script checks the PDF hash, compiled statement-index hash, all principal labels, reviewed definitions, proof entry points, dependency versions, and recursive theorem axioms. The [source hash inventory](../verification/source-hashes.json) records the current delivered inputs. The PDF publication and English documentation update leave every Lean source file byte-for-byte unchanged from the completed proof audit.

## Final acceptance

| Check | Result |
|---|---|
| Principal manuscript results | 19 / 19 VERIFIED |
| Local theorem axiom audit | 1,020 / 1,020 |
| Manuscript proof entry points | 54 / 54 |
| `sorry` | 0 |
| `admit` | 0 |
| Manuscript-specific axioms | 0 |
| RELATIVE_VERIFIED | 0 |
| WIP / BLOCKED | 0 / 0 |
| Compilation errors | 0 |
| Permitted foundational axioms | `propext`, `Classical.choice`, `Quot.sound` |

The complete project, manuscript, and verification records are available in the [GitHub repository](https://github.com/zhangteng2000/modified-cartan-lean).
