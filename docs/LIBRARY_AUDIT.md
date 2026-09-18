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

Searches for direct Harnack, Hurwitz, or Montel normal-family APIs did not locate a ready-to-use theorem in the initial search. This is not a proof of their absence. Harnack is now proved locally from Poisson; Hurwitz is now proved locally from `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, analytic uniqueness, and `Complex.norm_le_of_forall_mem_frontier_norm_le`. Inversion of locally uniform limits reuses `TendstoLocallyUniformlyOn.inv₀` from `Analysis/Normed/Field/Lemmas.lean`. Montel is now proved using `Complex.dist_le_div_mul_dist_of_mapsTo_ball`, `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`, the compact convergence uniformity on continuous maps, and `IsCompact.tendsto_subseq`. No connectedness assumption is needed for Montel.
