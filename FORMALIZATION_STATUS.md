# Formalization coverage

All 19 labeled manuscript results have complete Lean proofs. The table maps each result to its proof term and the corresponding PDF page. Proposition definitions alone do not count as completed proofs. The verification script checks the PDF and statement-index hashes, proof entry points, and the recursive axiom dependencies of all local theorems.

| Manuscript result | Status | Lean proofs and preserved scope |
|---|---|---|
| [1.2 (p. 2)](Modified%20Cartan%20conjecture.pdf#page=2) (`thm:main`) | VERIFIED | [partitionTheorem_proved](ModifiedCartan/PartitionTheorem.lean); [partition_at_recursive_radius](ModifiedCartan/PartitionTheorem.lean). All p >= 3; actual C-class partition after a common strict subsequence. The explicit radius r_(p-1)^(p-1) is proved as well. |
| [1.3 (p. 3)](Modified%20Cartan%20conjecture.pdf#page=3) (`thm:sharp-five`) | VERIFIED | [sharpFiveTheorem_proved](ModifiedCartan/SharpFive.lean). Arbitrary nonempty open subset of the unit disk, including disconnected sets; diameter <= log 3, with its endpoint. |
| [1.4 (p. 3)](Modified%20Cartan%20conjecture.pdf#page=3) (`thm:torus-zero`) | VERIFIED | [torus_manifold_metric_zero_iff](ModifiedCartan/TorusManifold.lean). Two-way equivalence for the intrinsic manifold Kobayashi-Royden metric. Finite Laurent equations plus an embedded complex manifold present the smooth closed subvariety; see [GEOMETRIC_MODEL.md](docs/GEOMETRIC_MODEL.md). |
| [2.1 (p. 5)](Modified%20Cartan%20conjecture.pdf#page=5) (`lem:cartan-circle`) | VERIFIED | [cartanCircleEstimate_proved](ModifiedCartan/CartanCircle.lean). 0 < a < b < c < 1; 0 < t <= 1 including t = 1; exact power t^gamma and radius in (b,c). |
| [2.2 (p. 6)](Modified%20Cartan%20conjecture.pdf#page=6) (`prop:wronskian`) | VERIFIED | [quantitativeWronskian_proved](ModifiedCartan/QuantitativeWronskian.lean). All m >= 1, normalized coefficient sphere, actual iterated-derivative determinant, c > 0 and K >= m. |
| [2.3 (p. 7)](Modified%20Cartan%20conjecture.pdf#page=7) (`lem:logderivative`) | VERIFIED | [logDerivativeEstimate_proved](ModifiedCartan/LogDerivativeEstimate.lean). All derivative orders k >= 1 and original radius intervals; exact logarithmic expression; boundary zeros allowed. |
| [2.4 (p. 8)](Modified%20Cartan%20conjecture.pdf#page=8) (`lem:growth`) | VERIFIED | [growthLemma_proved](ModifiedCartan/Growth.lean). The stated positive continuous nondecreasing case is proved; the internal construction also works without monotonicity. |
| [2.5 (p. 8)](Modified%20Cartan%20conjecture.pdf#page=8) (`lem:envelope`) | VERIFIED | [envelope_lemma](ModifiedCartan/Envelope.lean). Exact 8 and 64 constants, closed-disk supremum and all original parameter ranges; harmonic extension is separately constructed. |
| [2.6 (p. 9)](Modified%20Cartan%20conjecture.pdf#page=9) (`lem:poisson-mean`) | VERIFIED | [poissonMeanEstimate_proved](ModifiedCartan/LogPoisson.lean). Exact q and q^2 - 1 coefficients, analytic neighborhood of the closed disk, boundary zeros allowed. |
| [3.1 (p. 9)](Modified%20Cartan%20conjecture.pdf#page=9) (`thm:absorption`) | VERIFIED | [explicitAbsorptionTheorem_proved](ModifiedCartan/AbsorptionTheorem.lean); [absorption_at_recursive_radius](ModifiedCartan/AbsorptionTheorem.lean). Actual Wronskian exponent sequence is constructed; r1 = 1, r2 = 2 - sqrt 3 and r_m = r_(m-1)/(1024*(K_m+m)). |
| [3.2 (p. 13)](Modified%20Cartan%20conjecture.pdf#page=13) (`cor:rank-adaptive-absorption`) | VERIFIED | [rank_adaptive_absorption](ModifiedCartan/RankAdaptiveAbsorption.lean). Rank is the dimension of the span of restricted functions on the unit disk, for each n; exact r_d and one common subsequence. |
| [4.1 (p. 13)](Modified%20Cartan%20conjecture.pdf#page=13) (`lem:stabilization`) | VERIFIED | [stabilization_lemma](ModifiedCartan/QuotientStabilization.lean). Common subsequence on every sigma^k, actual quotient preorder, compact escape in sup norm and the stated maximal-class alternative. |
| [4.2 (p. 15)](Modified%20Cartan%20conjecture.pdf#page=15) (`cor:centers`) | VERIFIED | [partition_at_center](ModifiedCartan/PartitionCenters.lean). Pullback by the actual disk automorphism; same explicit epsilon_p. The partition and strict subsequence may depend on the center. |
| [5.1 (p. 16)](Modified%20Cartan%20conjecture.pdf#page=16) (`lem:two-point-kernel`) | VERIFIED | [two_point_harmonic](ModifiedCartan/HarmonicKernel.lean). All positive harmonic functions on the open unit disk; uniform positive epsilon_q, exact two weights. |
| [5.2 (p. 16)](Modified%20Cartan%20conjecture.pdf#page=16) (`cor:geodesic-comparison`) | VERIFIED | [geodesic_harmonic_comparison](ModifiedCartan/GeodesicComparison.lean). Entire distance-additive hyperbolic segment, including coincident endpoints; exact 2*C0 and uniform epsilon for d0 < log 3. |
| [5.3 (p. 17)](Modified%20Cartan%20conjecture.pdf#page=17) (`prop:sharp-two-absorption`) | VERIFIED | [sharpTwoAbsorption_proved](ModifiedCartan/SharpTwoAbsorption.lean). Arbitrary nonempty open sets; no connectedness requirement; non-strict diameter <= log 3. |
| [6.1 (p. 22)](Modified%20Cartan%20conjecture.pdf#page=22) (`prop:torus-null-set`) | VERIFIED | [torus_manifold_nullDirections_isClosed](ModifiedCartan/TorusManifold.lean); [torus_manifold_compact_metric_lower](ModifiedCartan/TorusManifold.lean); [torus_manifold_compact_inf_pos](ModifiedCartan/TorusManifold.lean); [torus_manifold_null_image_eq_zeroLocus](ModifiedCartan/TorusTangentAlgebraic.lean). Closed in the actual tangent bundle, equal to an explicit polynomial zero locus in (x,x^-1,v) coordinates, with a positive infimum on every compact set in the complement. |
| [6.2 (p. 23)](Modified%20Cartan%20conjecture.pdf#page=23) (`prop:projective-equivalence`) | VERIFIED | [projective_equivalence](ModifiedCartan/ProjectiveEquivalence.lean). Both directions, p >= 3 and 0 < R <= 1; genuine projective quotient topology, product uniformity and manifold holomorphic maps. |
| [6.3 (p. 23)](Modified%20Cartan%20conjecture.pdf#page=23) (`cor:projective-zero-directions`) | VERIFIED | [projective_zero_directions](ModifiedCartan/ProjectiveTori.lean); [projectiveTorusTangentSpace_finrank_le](ModifiedCartan/ProjectiveTori.lean). Exact union of differential images of actual holomorphic torus embeddings, with dimension <= floor(p/2)-1. |

Definition 1.1 (`def:cclass`) corresponds to `IsDominant`, `IsCClass`, and `CPartition` in [Basic.lean](ModifiedCartan/Basic.lean). The dominant index belongs to the class, making it nonempty. Bounds hold on every compact set for all sequence terms, and convergence is uniform on compact sets. The predicates apply to arbitrary sets and hence to the regions used in the paper's definition.

## Supplemental results

- **cartan-extraction-required-by-paper**: `cartanExtraction_three`, `cartanExtraction_four`, `cartanExtraction_five`.
- **optimal-five-radius**: `optimalFiveRadius_proved`, `partition_five_at_sharpRadius`.
- **gaussian-holomorphic-branch**: `fivePhi_differentiable`, `fiveL_differentiable`, `fivePhi_sq`.
- **gaussian-majorants-and-sign**: `five_majorant_positive_gap`, `fiveL_re_pos_right`, `fivePhi_re_nonpos_iff`, `fivePhi_re_nonneg_iff`.
- **gaussian-integral-and-tail**: `gaussianPrimitive_hasDerivAt`, `gaussianTransition_left_bound`, `gaussianTransition_right_bound`.
- **gaussian-exact-ratio-estimate**: `fivea_div_fiveA_bound`, `fivea_complement`.
- **gaussian-five-units-and-zero-sum**: `fiveCounterexample_units`, `fiveCounterexample_zeroSum`.
- **gaussian-growth-and-vanishing**: `fiveCounterexample_grows_at_zero`, `fiveA_vanishes_negative_point`, `fivea_sub_fiveA_vanishes_negative_point`, `fiveCounterexample_vanishing_points`.
- **gaussian-no-partition-any-subsequence**: `fiveCounterexample_no_partition`.
- **disk-diameter-formula**: `disk_hyperbolicDiameter_iff`, `sharpRadius_log_diameter`, `sharpRadius_hyperbolicDiameter`.
- **sharp-diameter-obstructions**: `five_partition_diameter_cannot_increase`, `two_absorption_diameter_cannot_increase`.

The classical p = 5 Cartan extraction on the entire unit disk is proved and used in the sharp-five theorem. The p = 3 and p = 4 cases are proved as supporting results. The unused historical arbitrary-p version is outside the completion claim.

## Mathematical correspondence

- `exists_wronskianExponents` constructs valid Wronskian exponents for the recursive radii; these are not additional analytic assumptions.
- The open-set theorems allow disconnected sets. The diameter bound remains `≤ log 3`, and the projective statements retain `0 < R ≤ 1`.
- All extracted subsequences are strictly increasing. All locally uniform limits use actual uniform convergence on compact sets.
- The geometric results use mathlib manifold tangent spaces, differentials, the projective quotient topology, and product uniform structures. Finite Laurent equations present the closed algebraic locus; see [GEOMETRIC_MODEL.md](docs/GEOMETRIC_MODEL.md).
- The Kobayashi-Royden pseudometric takes values in the nonnegative extended reals, so an empty infimum is positive infinity.

Final counts, fresh-build evidence, and axiom audits are recorded in [result.json](verification/result.json) and the [final report](docs/FINAL_REPORT.md). The theorem count includes auxiliary lemmas and is not a percentage of manuscript completion.
