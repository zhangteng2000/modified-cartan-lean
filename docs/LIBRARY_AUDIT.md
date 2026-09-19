# Pinned mathlib audit

Version: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`. Paths below are relative to its `Mathlib` directory. This is an API audit of the installed source, not an assumption that every named mathematical theorem is already formalized.

| Needed result | Located source / declarations | Use |
|---|---|---|
| Poisson representation | `Analysis/Complex/Harmonic/Poisson.lean`; `HarmonicContOnCl.circleAverage_poissonKernel_smul` | exact representation including continuous boundary data |
| Poisson kernel bounds | `Analysis/Complex/Poisson.lean`; `re_herglotzRieszKernel_le`, `le_re_herglotzRieszKernel` | derive Harnack without adding hypotheses |
| Circle averages | `MeasureTheory/Integral/CircleAverage.lean`; monotonicity, nonnegativity, linearity | integrate pointwise kernel comparisons |
| Harmonic boundary regularity | `Analysis/InnerProductSpace/Harmonic/HarmonicContOnCl.lean` | differences and restriction of harmonic functions |
| Canonical factors | `Analysis/Complex/CanonicalDecomposition.lean` | factors have poles at their parameter (reciprocal of the usual Blaschke convention); check signs when reusing |
| Jensen formula | `Analysis/Complex/JensenFormula.lean` | inspect for logarithmic mean estimates with zeros |
| Complex locally uniform limits | `Analysis/Complex/LocallyUniformLimit.lean` | preservation of holomorphicity |
| Exponential independence | Vandermonde matrix results | already reused in `Exponential.lean` |
| Finite preorders | `Order/Preorder/Finite.lean`; `Finset.exists_le_maximal` | choose maximal indices above each index; all class-count and stability arguments proved locally |
| Finite cardinalities | `Fintype.card_le_of_injective`, `Fintype.card_lt_of_injective_not_surjective` | inject new maximal classes into old ones; equality makes the injection surjective |
| Analytic removal of zeros | `Function.FactorizedRational.meromorphicOrderAt_eq`, `toMeromorphicNFOn`, `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` | construct the analytic quotient by any finite effective zero divisor, including values at zeros |
| Logarithmic radial averaging | `intervalIntegral.integral_log`, `intervalIntegrable_log'`, `Real.abs_log_mul_self_lt`, `integral_mono_ae_restrict` | a uniform integral bound and a radius avoiding finitely many singular moduli |
| Cauchy derivative estimate | `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` | uniform derivative-jet and Wronskian upper bounds on smaller disks |
| Matrix determinant/inverse | `Matrix.det_updateCol_sum`, `Matrix.det_succ_column`, `Matrix.adjugate_apply`, `Matrix.mul_nonsing_inv` | exact Wronskian residual, analytic coefficient functions and inverse-entry bounds |
| Circle variation | `hasDerivAt_circleMap`, `HasDerivAt.scomp`, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` | derivative control around a whole circle; no fictitious interior extension of the coefficients |
| Real powers | `Real.mul_rpow`, `Real.rpow_mul`, `Real.rpow_le_rpow_of_exponent_ge` | preserve the original power dependence and arrange K ≥ m |
| Holomorphic primitives | `DifferentiableOn.isExactOn_ball`, `Complex.IsExactOn.with_val_at` | construct a holomorphic logarithm by integrating Q′/Q and proving Q exp(−L) = 1 |
| Real-part growth | `Complex.borelCaratheodory_zero` | remove the constant from the holomorphic logarithm before Cauchy differentiation |
| Angular domination | `Real.cos_le_one_sub_mul_cos_sq`, `intervalIntegral.intervalIntegrable_rpow'`, `Function.Periodic.intervalIntegrable` | uniform integrability of fractional pole powers, with poles on the circle allowed |
| Logarithmic product rules | `logDeriv_prod`, `logDeriv_fun_pow`, `iteratedDerivWithin_one_div`, `Set.EqOn.iteratedDeriv_of_isOpen` | actual finite-factor identities and higher principal-pole derivatives |

Searches for direct Harnack, Hurwitz, or Montel normal-family APIs did not locate a ready-to-use theorem in the initial search. This is not a proof of their absence. Harnack is now proved locally from Poisson; Hurwitz is now proved locally from `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, analytic uniqueness, and `Complex.norm_le_of_forall_mem_frontier_norm_le`. Inversion of locally uniform limits reuses `TendstoLocallyUniformlyOn.inv₀` from `Analysis/Normed/Field/Lemmas.lean`. Montel is now proved using `Complex.dist_le_div_mul_dist_of_mapsTo_ball`, `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`, the compact convergence uniformity on continuous maps, and `IsCompact.tendsto_subseq`. No connectedness assumption is needed for Montel.

## Logarithmic derivative completion

Used mathlib meromorphic closure under derivatives, local circle integrability of log⁺ norms, analytic isolated-zero/codiscrete results, `iteratedDeriv_fun_mul` and finite sum bounds. Adapted proximity sum/product estimates to functions meromorphic only near the integration circle, since global meromorphicity is not a manuscript hypothesis. Fractional moments and exact radius-gap dependence are proved in project modules. No extra zero-free or boundary-zero exclusion hypothesis was introduced.

## Absorption preparations and constructed Poisson extension

The compact-exhaustion and locally uniform convergence APIs are used for the failure-point alternative, without a connectedness assumption. Compactness of the finite-dimensional coefficient sphere supplies actual minimizers. The Herglotz integral APIs `analyticOnNhd_circleAverage_herglotzRieszKernel_smul` and `re_circleAverage_herglotzRieszKernel_smul` construct the harmonic extension, while library kernel bounds and the harmonic mean-value property prove monotonicity of the growth mean. Finite holomorphic zero factorization provides the zero-free annulus. The full library axiom audit at this checkpoint covers 317 declarations.

## Wronskian scaling, boundary integration and asymptotics

`iteratedDeriv_comp_const_mul` requires global smoothness, so input scaling is instead proved locally from analytic jets, eventual equality and the derivative chain rule. Library determinant column scaling then yields the exact triangular exponent. `Matrix.det_updateCol_sum` supplies the sum-column replacement identity without a sign ambiguity. Library meromorphic logarithm integrability and codiscrete-circle measure comparison justify both mean estimates even with boundary zeros. `Real.isLittleO_log_id_atTop`, finite little-o sums and locally uniform derivative convergence supply the vanishing error.

### Sharp two-term geometry and moving points

Reused mathlib Blaschke factors, harmonic conjugates on balls, compact finite subcovers, and the complex maximum principle. Proved disk automorphism formulas, two-point Harnack comparison, strict compact pseudodiameter for arbitrary open sets, actual symmetric disk-segment maps, and a fixed compact zero-free failure-point set. Moving-point convergence is derived from compact convergence. These are supporting results; sharp two-term absorption is still WIP.

The 412-declaration checkpoint additionally uses compact uniform-neighborhood quantification (`IsCompact.eventually_forall_of_forall_eventually`), analytic isolated-zero codiscrete filters, and the actual Harnack estimates. Poisson comparison is proved through integrals and handles identically zero Wronskians explicitly. No geodesic-existence or path-integral conclusion has been assumed.

At 435 declarations, mathlib compact parameter uniformization, two-segment countable avoidance, and the connected-space induction principle have been instantiated and proved. The countable-avoidance argument is localized from mathlib Analysis/Normed/Module/Connected.lean using openness at the midpoint. It constructs paths rather than assuming zero-free connectivity.

Sharp two-term absorption is now fully proved using mathlib compactness, holomorphic convergence, harmonicity, real mean-value estimates and finite-zero-set results. The manuscript-specific coordinate construction, fixed rectangle decay and final contradiction are proved locally, with no additional axioms. Audited at 460 declarations.

Partition and rank-adaptive checkpoint: mathlib finite sums, finite-dimensional span monotonicity and finite dependence supply the algebraic interfaces. The actual maximal-class assignment, uniform escape witnesses, normalized-limit contradiction, full partition assembly, automorphism transport and bounded elimination are proved locally. Full audit: 490 declarations, standard axioms only.

Algebraic null locus: uses Mathlib.RingTheory.Nullstellensatz zeroLocus_span and actual MvPolynomial evaluation. No Nullstellensatz existence theorem or additional algebraic axiom is needed. Manifold audit: Immersion.lean supplies smoothness recovery through an immersion, but differential injectivity remains a library TODO; a local-left-inverse proof is being developed.

The missing immersion differential injectivity result is now proved locally, without a supplied assumption: build a C¹ local left inverse from the immersion charts and differentiate its local identity. Mathlib tangentBundleModelSpaceHomeomorph and ContMDiff.continuous_tangentMap supply the actual tangent-bundle continuity used for compactness.

2026-09-19: mathlib `LinearAlgebra.Projectivization.Basic` supplies the actual projective quotient, scalar equivalence, and representatives. No general projectivization topology/manifold instance was found in the pinned topology/manifold tree; quotient-topological affine charts are being constructed using `IsQuotientMap.restrictPreimage_isOpen`. Finpartition supplies actual finite partitions; no abstract partition axiom is used.

Projective geometry now constructed: standard quotient topology via mathlib IsQuotientMap, open affine charts, singleton complex manifold atlas, finite-dimensional complementary subspaces for immersion charts, and actual mfderiv chain rule. The derived immersion injectivity and affine differential statements fill the missing pinned-library bridges. No projective metric equivalence is assumed.

Geodesic comparison uses Mathlib.Analysis.Complex.Schwarz for Schwarz-Pick via conjugation, then explicit real logarithmic distance formulas and complex norm identities. Both directions of the exact geodesic image identity are proved locally; no metric-segment identification is assumed.

Gaussian estimates reuse mathlib Complex.wedgeIntegral, its holomorphic primitive theorem, integral_gaussian_Ioi, improper-integral convergence and Gaussian exponential decay. The contour-shift identity, finite contour estimates and exact limiting half-plane bounds are proved in project modules.

The explicit square-root branch uses Complex.sqrt from the pinned RCLike/Pow API and Complex.differentiableAt_sqrt on the slit plane, with Re(1-z^4)>0 proved on the unit disk. Real-part sign is proved by an explicit positive algebraic factor. The five-function nonpartition argument handles every strictly increasing extraction and uses the exact project C-class predicate. No counterexample existence assumption is introduced.

Projective convergence audit: mathlib Projectivization is given its genuine quotient topology. A scalar-invariant coordinate matrix proves Hausdorffness; the unit sphere gives compactness; uniformSpaceOfCompactR1 supplies the compatible uniformity. Existing locally uniform convergence, finite-dimensional compactness, manifold immersion and finite partition APIs are used. Global projective Hurwitz and both geometric partition implications are proved, with no chart-avoidance assumption on the limit.

Classical Cartan extraction source: Henri Cartan, Ann. Sci. ENS 45 (1928), Theorem VII, pp. 312-315, DOI 10.24033/asens.786, https://www.numdam.org/articles/10.24033/asens.786/. The original pages have been read; no cited theorem is introduced as a Lean axiom. The analytic extraction proof remains unfinished. The local mathlib complex-analysis Cartan namespace concerns a different integral formula and does not supply this extraction theorem.

Classical extraction preparation: existing holomorphic-log construction, mathlib convex mean-value bounds and the previously proved Montel/Hurwitz/failure-point tools prove LogDerivativeNormality. The finite five-index classification uses mathlib finite-set cardinality; the analytic assembly uses the already proved sharp_two_absorption without a connectedness assumption. These are auxiliary proofs, not a proof of the still-open CartanExtractionAt target.

Normality: reused mathlib ArzelaAscoli.isCompact_closure_of_isClosedEmbedding, compact sequential extraction, Continuous.isClosedEmbedding, and IsEmbedding.toHomeomorph. Proved the missing implication from local subsequence limits to equicontinuity directly by a bad-sequence contradiction. No separate Picard, Montel, or Cartan theorem is postulated.

The further Cartan steps reuse mathlib finite extraction from frequently occurring indices, strict extraction of a sequence tending to infinity, the finite-subcover theorem, maximum-modulus principle, Fin.succAbove and existence of its inverse away from the deleted index, and connectedness of a sphere in real dimension greater than one. All zero-free annuli, shifted merged units, quotient bounds, and index lifting are proved in the project.

For the higher Cartan cases, reused Complex real logarithm derivatives and ContinuousLinearMap derivative composition, determinant Laplace expansion, Bochner Markov inequalities and meromorphic circle integrability. No pre-existing classical Cartan extraction theorem is imported. Normalized Wronskian proximity control and quantitative radial exceptional sets are proved locally.

The 908-declaration checkpoint reuses finite-dimensional determinant multiplication, Leibniz iterated derivatives, finite geometric series in ENNReal, real monotone-function level sets, asymptotic logarithmic smallness and circle Poisson bounds. The actual growth exceptional cover, common-factor determinant cancellation and radial proximity exception estimates are proved locally, without invoking an unformalized Cartan theorem.
