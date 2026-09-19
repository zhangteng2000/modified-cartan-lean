# Geometric model and correspondence

The torus theorems use a finite Laurent presentation and a complex embedded manifold. This is the coordinate presentation of the manuscript's smooth closed algebraic subvariety hypothesis:

- TorusEquations records finitely many finite Laurent sums. Each recorded term has nonzero coefficient; zero equations have no terms, and the full torus has no equations. Repeated exponents are allowed. The locus is the common zero set inside the actual nonzero-coordinate torus.
- M has a mathlib ChartedSpace over a complex model E and IsManifold of class C¹ over ℂ. The map e : M → ℂᴺ is a topological embedding and a complex C¹ immersion whose range is the Laurent locus. For the subvariety itself, e is its inclusion. These express smoothness and the given embedded topology, not an extra analytic estimate or a metric assumption. The conclusions hold for any such presentation and do not depend on distinct exponent vectors or irreducibility.
- Tangent vectors and the tangent-bundle topology are mathlib TangentSpace and TangentBundle. The ambient vector is mfderiv e x v, not an independently supplied vector.
- ManifoldTangentDisc uses MDifferentiableOn over ℂ, a center equality, and the actual manifold derivative applied to 1. The infimum uses exactly t > 0 and 1/t. As usual for locally defined functions in Lean, the disk map is extended arbitrarily outside the open unit disk; no regularity or image condition is imposed there.

ManifoldDiscs proves both translations of admissible disks and equality of the resulting metric values. The reverse translation constructs the lift from the embedding, recovers holomorphicity using immersion charts, and recovers the tangent equality from a proved injective differential. ImmersionDifferential establishes that injectivity by differentiating a constructed local left inverse.

Theorem torus_manifold_metric_zero_iff is the original two-way zero-direction criterion in these intrinsic coordinates. TorusManifold also proves closedness in the actual tangent bundle and a strictly positive infimum on every compact set outside the null set.

For algebraicity, the affine coordinates are (x, x⁻¹, v). The explicit ideal contains xⱼ yⱼ − 1 and the first q moment polynomials for every defining Laurent equation with q terms. TorusTangentAlgebraic proves equality of the entire polynomial zero locus with the image of the intrinsic null directions. The reverse inclusion constructs an actual exponential curve, lifts it to M, and differentiates it to recover an intrinsic tangent vector. Thus it is not merely a list of candidate equations or a conditional finite-moment lemma.

These results concern thm:torus-zero and prop:torus-null-set. The projective charts, projective convergence equivalence and projective torus tangent/dimension assertions still require separate proofs.

## Projective application

`ProjectiveX p` is the zero-sum, coordinate-hyperplane-complement subset of mathlib projectivization. `ProjectiveTopology` uses the quotient topology of nonzero complex vectors; it does not assign a topology by an unverified bijection. The affine chart is proved to be a homeomorphism. Subtracting a fixed normalized point identifies X_p with an open set in the complex linear space {v_k=0, sum v_j=0}; this supplies the standard complex manifold. Nonemptiness is proved for p >= 2, so the manuscript p >= 3 introduces no extra assumption.

The projective tori are actual holomorphic topological embeddings of open affine subspaces, with injective manifold differential at every point. Their images agree with the manuscript nonzero part-scaling parameterization. Their tangent spaces are defined as images of these actual differentials at the point mapped to x. The exact zero-direction set and the dimension bound floor(p/2)-1 are proved, including one-part partitions and diagonal hyperplanes.

## Projective partition equivalence

Projectivization is equipped with its actual quotient topology, proved compact and Hausdorff, and the compatible compact-space uniformity. ProjectiveHolomorphicOn is holomorphy in the standard affine coordinate homeomorphisms: each coordinate ratio must be complex differentiable where its denominator is nonzero. ProjectiveProductHolomorphicOn uses these charts componentwise in the genuine product of projective spaces. projectiveX_holomorphic_iff proves agreement with MDifferentiableOn for the already constructed X_p complex manifold. projective_equivalence quantifies over those actual manifold-valued holomorphic maps, constructs actual coordinate projections, and uses TendstoLocallyUniformlyOn into the true product uniformity. The limit is required to map D(R) into the product of the zero-sum hyperplanes. The global affine denominator is derived from hyperplane Hurwitz, not supplied as an extra hypothesis. All radii 0 < R <= 1 and dimensions p >= 3 are retained.
