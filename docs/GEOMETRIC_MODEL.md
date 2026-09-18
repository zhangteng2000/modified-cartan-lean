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
