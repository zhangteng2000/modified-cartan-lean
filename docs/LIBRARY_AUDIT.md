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

Searches for direct Harnack, Hurwitz, or Montel normal-family APIs did not locate a ready-to-use theorem in the initial search. This is not a proof of their absence. Harnack is now proved locally from Poisson; Hurwitz is now proved locally from `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, analytic uniqueness, and `Complex.norm_le_of_forall_mem_frontier_norm_le`. Inversion of locally uniform limits reuses `TendstoLocallyUniformlyOn.inv₀` from `Analysis/Normed/Field/Lemmas.lean`. Montel is now proved using `Complex.dist_le_div_mul_dist_of_mapsTo_ball`, `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`, the compact convergence uniformity on continuous maps, and `IsCompact.tendsto_subseq`. No connectedness assumption is needed for Montel.
