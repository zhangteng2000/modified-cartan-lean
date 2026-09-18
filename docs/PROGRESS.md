VERIFIED: Manuscript lem:cartan-circle, prop:wronskian, lem:logderivative, lem:growth, lem:envelope, lem:two-point-kernel, lem:poisson-mean, lem:stabilization, and the connected two-dominant-index assertion fully proved; declaration count in verification/result.json.
RELATIVE_VERIFIED: 0
WIP: Full manuscript; absorption, partition theorem and geometric applications.
BLOCKED: No external blocker. Unproved mathematical dependencies are recorded below.
SORRY_COUNT: 0
USER_AXIOM_COUNT: 0

# Full formalization progress

The goal is the full manuscript, with the original hypotheses, constants, explicit radii, endpoint inequalities, and equivalences. A definition of a proposition is not a proof. Declaration counts include elementary auxiliary results and do not measure a percentage of manuscript completion.

## Reproducible baseline

- Lean: `leanprover/lean4:v4.34.0-rc1`.
- mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.
- Baseline `lake build`: success, 3397 jobs; all 59 proof declarations audited.
- Permitted axioms seen: `propext`, `Classical.choice`, `Quot.sound` only.
- `paper.tex` is the supplied manuscript. Statements are located by its LaTeX labels.

## Phase 0 — setup and audit

- [x] Read manuscript, existing project and the user's full execution requirements.
- [x] Rebuild and audit the existing proof terms.
- [x] Pin Lean/mathlib and preserve the manuscript source.
- [x] Record the dependency graph, library audit, discrepancies and blockers.
- [ ] Complete exact formal statements for every remaining manuscript result.

## Phase 1 — analytic tools

| Result | Status | Remaining proof work |
|---|---|---|
| `lem:cartan-circle` | VERIFIED | `cartanCircleEstimate_proved : CartanCircleEstimate`; exact t^γ, γ depending only on a,b,c, including t = 1 |
| `prop:wronskian` | VERIFIED | `quantitativeWronskian_proved : QuantitativeWronskian`; all m ≥ 1 and 0 < a < b < 1, genuine determinant and coefficient sphere, c > 0 and K ≥ m |
| `lem:logderivative` | VERIFIED | `logDerivativeEstimate_proved : LogDerivativeEstimate`; exact original mean bound for every k, all zeros and all allowed radii |
| `lem:growth` | VERIFIED | `growthLemma_proved : GrowthLemma` |
| `lem:envelope` | VERIFIED | `envelope_lemma`; exact 8δ and 64η constants and closed-disk supremum |
| `lem:poisson-mean` | VERIFIED | `poissonMeanEstimate_proved : PoissonMeanEstimate`; boundary zeros permitted |
| `lem:two-point-kernel` | VERIFIED | `two_point_harmonic`; all positive harmonic functions on the open unit disk |

## Phases 2–4 — principal results and applications

| Result | Status | Remaining proof work |
|---|---|---|
| `prop:sharp-two-absorption` | WIP | harmonic comparison, path selection and contradiction |
| `thm:absorption` | WIP | `ExplicitAbsorptionTheorem` now includes exact radii and valid Wronskian exponents; analytic induction remains |
| `cor:rank-adaptive-absorption` | WIP | minor selection and subsequence basis |
| `lem:stabilization` | VERIFIED | `stabilization_lemma`; common extraction, actual quotient preorders, maximal-class counting and incomparability |
| `thm:main`, `cor:centers` | WIP | stabilization/absorption assembly and disk automorphisms |
| `thm:sharp-five` | WIP | classical Cartan extraction and sharp absorption; arbitrary open U retained |
| optimal five-function radius | WIP | Gaussian integral counterexample and exact extremal argument |
| `thm:torus-zero` | WIP | forward direction from an orbit is proved; converse and geometric identification remain |
| `prop:torus-null-set` | WIP | finite equations proved; closedness/algebraicity and positive compact lower bounds remain |
| `prop:projective-equivalence` | WIP | projective formalism and both implications |
| `cor:projective-zero-directions` | WIP | quotient tangent-space identification and dimension bound |

Final completion requires genuine proof terms for every row, no placeholder or manuscript-specific axioms, successful full build and recursive axiom audit, and a theorem-by-theorem comparison against `paper.tex`. No final report exists yet.

## Verified analytic checkpoint

`Harmonic.lean` proves both centered Harnack inequalities directly from the library Poisson formula and proves boundary nonnegativity implies interior nonnegativity. `Envelope.lean` proves `lem:envelope` for the harmonic extension U of the positive boundary maximum. The extension is represented by `HarmonicContOnCl` plus the exact boundary-maximum equality (`IsGreatest`), matching the manuscript's given U. The origin estimate and supremum estimate have the original constants.

Git initialized in the deliverable directory; no remote is configured, so no push target exists.

`HarmonicKernel.lean` connects the real rational kernel to mathlib's complex Poisson kernel, integrates the uniform inequality on circles of radius R, and passes to R → 1 from below. Thus `two_point_harmonic` assumes no boundary continuity on the unit circle and proves the full manuscript lemma, with a single positive ε depending only on q.

`LogPoisson.lean` proves Poisson comparison for logarithmic factors with zeros in the closed disk, including boundary zeros using mathlib's integrability theorem. Finite zero-factor extraction then gives the comparison for any analytic F nonzero at the evaluation point. Integrating the upper and lower kernel bounds proves the manuscript's exact q log|F(w)| − (q²−1)m(R,F) bound. `poissonMeanEstimate_proved` has the original normalized q = (1+t)/(1−t), t = |w|/R.

`Convergence.lean` proves preservation of C-classes and partitions under subsequences, finite simultaneous extraction, transitivity of locally bounded quotients, the exact change-of-dominant-index criterion, boundedness of convergent continuous families including initial terms, and holomorphic/derivative limit interfaces. These results do not assume connectedness.

`Hurwitz.lean` proves Hurwitz nonvanishing on a connected open set, inversion of locally uniform limits, and boundedness of their reciprocals. `Montel.lean` proves locally bounded holomorphic families are equicontinuous and admits a convergent subsequence on any open subset, using Schwarz and mathlib's Arzelà–Ascoli theorem. `CClass.lean` combines simultaneous Montel extraction with Hurwitz to prove `cclass_two_dominants_after_extraction` in full. The connectedness hypothesis occurs in this auxiliary assertion, not in the C-class definition or the main/sharp targets.

`Extraction.lean` proves simultaneous holomorphic-limit-or-compact-supremum-divergence alternatives, including their equivalence to boundedness/unboundedness after extraction. `FinitePreorder.lean` counts actual maximal equivalence classes as finite sets, constructs the injection between successive maximal-class sets, and proves incomparability when the counts agree. `QuotientStabilization.lean` combines them into the full `lem:stabilization` for the manuscript radii σ^k, 0 < σ < 1, on a nonempty finite family. No analytic or order-theoretic conclusion is supplied as an extra hypothesis.

`CartanCircle.lean` proves the full Cartan circle estimate. `ZeroFactors.lean` removes all zeros with multiplicity in a fixed closed smaller disk while preserving analyticity on the whole unit disk. `BlaschkeDecomposition.lean` uses factors normalized on a larger circle, so boundary zeros of the smaller disk require no exceptional-radius choice. `Blaschke.lean` proves uniform contraction and the radial lower bound. `RadialLog.lean` proves integrability, a uniform integral estimate, and weighted radius selection avoiding all zero moduli. `CartanAux.lean` proves the logarithmic zero count and Harnack bound for the zero-free remainder. All constants depend only on the fixed radii. The final proof also works at t = 1 without a separate case.

`CauchyBounds.lean` proves uniform bounds for every derivative jet, analyticity of Wronskians, and a positive explicit upper bound for all bounded holomorphic families on each smaller disk. `CombinationNorm.lean` proves attainment and homogeneity of the disk supremum, 0 ≤ Λ ≤ 1, the normalized and unnormalized coefficient inequalities, and monotonicity when the last function is removed.

`WronskianAlgebra.lean`, `WronskianDifferentiation.lean`, `MatrixAnalytic.lean` and `WronskianCoefficients.lean` prove the determinant residual identity, analytic inverse entries and the exact derivative identity for the actually defined coefficients d = Y⁻¹v. `CircleVariation.lean` controls variation on a full circle without requiring holomorphic coefficients in its interior. `WronskianCoefficientBounds.lean` and `WronskianCircle.lean` combine Cauchy/cofactor bounds, circle variation and the maximum principle into Λ times the squared minor lower bound ≤ C times the full Wronskian supremum. `CartanScaled.lean` transports the proved circle lemma to an arbitrary smaller disk with exact scalar normalization. `WronskianPower.lean` proves the required real-power algebra. `QuantitativeWronskian.lean` completes the dimension induction, including Λ = 0 and increasing the exponent to K ≥ m. This proves the original proposition in full without any independence hypothesis.

`WronskianExponents.lean` produces valid exponents for all dimensions at a = 1/4, b = 1/2 with K₁ = 1. `ProximityGrowth.lean` proves pointwise Poisson/proximity comparison and the local bound |h| ≤ exp(1 + 4 m(R,h)/(R-r)) on the closed midpoint disk. These provide the initial analytic estimates used by the completed logarithmic-derivative proof.

`BlaschkeQuantitative.lean` proves the explicit uniform contraction |b(a,S)(w)| ≤ exp(−c d), c = r₀(r₀²−α²)/8 > 0, when the zero is at least d inside the outer circle. `ZeroCount.lean` derives the count with multiplicities N ≤ (H + log⁺(1/τ))/(c d), along with the actual finite factorization and zero-free remainder. The boundary-bound form of `bounded_blaschke_factorization_local` avoids assuming a uniform bound on the entire unit disk.

`HolomorphicLog.lean` constructs a genuine holomorphic logarithm on a zero-free disk by taking a primitive of Q′/Q. `ZeroFreeGrowth.lean` applies Harnack to H − log|Q| and obtains its origin bound from an off-center lower bound. `RealPartCauchy.lean` derives all higher Cauchy estimates from Borel–Carathéodory after removing the constant value at the origin. `ZeroFreeLogDerivatives.lean` combines them into the explicit all-orders derivative estimate for the constructed logarithm, retaining the dependence on H + log⁺(1/τ). Pole bounds and angular integration are supplied by the later modules below.

`LogarithmicPoles.lean` proves the finite-product logarithmic derivative identity, the actual Blaschke factor decomposition into principal and reflected poles, all iterated derivatives of the principal reciprocal pole, and the reflected-pole norm bound. The higher-order product assembly, logarithmic mean bound and final polynomial conversion are completed below.

`AngularGeometry.lean` proves the exact squared-distance formula, angular distance lower bound, real-pole fractional-power domination and rotation identity. `AngularIntegrals.lean` proves absolute-power integrability, a uniform bound for every complex pole and every radius bounded away from zero, including poles on the integration circle. `angular_inverse_powers_finite` supplies one constant simultaneously for 1 ≤ j ≤ k with exponent j/(2k), completing the manuscript's `eq:angular-integrability`. The full logarithmic-derivative mean estimate is completed by the later modules below.

`ReflectedDerivatives.lean` proves all higher reflected-pole derivative bounds and combines them with the principal-pole formula. `LogDerivativeProducts.lean` differentiates the actual finite product identity to every order and identifies the derivatives of Q′/Q with derivatives of the constructed logarithm. `FinitePoleBounds.lean` sums the bounds with multiplicities for an actual Blaschke factorization, on the smaller disk away from its finite zero set. The explicit constants and logarithmic means are assembled by the later modules below.

`ProximityMoment.lean` proves the logarithmic moment inequality m(r,f) ≤ p⁻¹ log(1 + mean |f|^p) for every p > 0 when the displayed functions are circle integrable. It uses the tangent inequality for log and actual circle-average linearity. The later pole-bound and recurrence modules apply this inequality with uniform constants and complete the conversion to h^(k)/h.

`FractionalPowers.lean`, `CircleExceptional.lean` and `PoleMoments.lean` prove the weighted fractional-power estimate, integration across codiscrete exceptional sets, and the logarithmic mean bound for finite pole sums. `ProximityLocal.lean` proves local-circle sum/product/congruence estimates for meromorphic functions.

`LocalLogDerivativePoles.lean` assembles the actual factorization, zero count and zero-free logarithm bounds for all orders. `LogDerivativeConstants.lean` bounds all regular terms by a fixed polynomial in the inverse radius gap; `LogarithmicGrowthAlgebra.lean` converts these to the required logarithmic scale. `IteratedLogDerivativeMean.lean` proves the uniform estimate for every iterated derivative of h′/h, including zeros on the integration circle. `DerivativeQuotientRecurrence.lean` proves the actual Leibniz recurrence and its proximity inequality. `LogDerivativeEstimate.lean` completes the strong induction for h^(k)/h and proves `logDerivativeEstimate_proved : LogDerivativeEstimate` with the exact original assumptions and logarithmic error. This manuscript lemma is now fully proved.

`HolomorphicCancellation.lean` proves cancellation across zeros of a nontrivial holomorphic limit using locally chosen surrounding circles and the maximum principle. It then proves the exact one-term absorption statement `absorption_one : AbsorptionAt 1 (disk 1)` on the full unit disk. This completes the m = 1 base case; the two-term sharp case and general induction remain WIP.

`FailurePoints.lean` constructs a diagonal subsequence using a compact exhaustion of any open complex set. Its contrapositive gives a fixed compact set and uniform lower bound for reciprocals, hence logarithmic failure points. Connectedness is not assumed. `Rescaling.lean` proves compact convergence under domain composition and transports `AbsorptionAt` to any concentric source disk. `CombinationMinimum.lean` proves compactness of the normalized coefficient sphere, continuity and attainment of the least combination norm, and the maximal-coefficient bounds required for removing one term.

`FiniteFailurePoints.lean` selects one compact set and one nonnegative logarithmic bound for an entire finite family. `AbsorptionLinearAlgebra.lean` proves the removal identity, reciprocal bound for a maximal unit coefficient, fixed-index extraction and compact convergence from a vanishing disk supremum. `AbsorptionPreparations.lean` provides a zero-convergent subsequence when a nonnegative scalar sequence has no eventual positive lower bound, and nontriviality on smaller disks.

`AbsorptionReduction.lean` constructs the actual family with one term removed and transports lower-dimensional absorption to it. `AbsorptionGap.lean` proves the absolute gap for the least normalized combination norm under the induction hypothesis and failure of all reciprocal conclusions. This is the manuscript induction step’s first analytic subargument; it does not prove the full absorption theorem, whose growth/Wronskian contradiction and sharp two-term base case remain open.

`PoissonExtension.lean` defines the actual extension through the Herglotz integral and proves its harmonicity, center value and comparison with harmonic boundary data. `HarmonicGrowth.lean` proves continuity and monotonicity in radius of the circular mean of max(0,u₁,…,uₘ) for a finite harmonic family, by comparing with this constructed extension. No existence of an envelope is assumed in these new construction results.

`PoissonHarnack.lean` proves both centered Harnack bounds for the constructed extension. `PoissonEnvelope.lean` obtains the original 8δ and 64η constants directly from boundary data and failure points. `ZeroFreeAnnulus.lean` constructs an actual annulus avoiding every zero of the nontrivial limit and transfers a positive lower bound to the approximating sums. `UnitGrowth.lean` proves divergence of the circular growth mean from the absorption hypotheses. `GrowthSelection.lean` selects actual radii with the inverse-growth gap and doubling bound.

Checkpoint: 317 proof declarations, 3582 successful build jobs, complete source coverage in the axiom audit, and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. Full absorption, partition and geometric theorems remain WIP.
