import ModifiedCartan.TorusManifold

noncomputable section
set_option autoImplicit false
open Set Filter Topology Manifold
open scoped Manifold ContDiff ENNReal
namespace ModifiedCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) 1 M]

theorem torus_manifold_null_tangent_image {N : ℕ} (L : TorusEquations N)
    {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (hrange : range e = L.locus) :
    tangentCoordinates (E := E) e '' manifoldNullDirections =
      {w : (Fin N → ℂ) × (Fin N → ℂ) |
        w.1 ∈ L.locus ∧ kobayashiRoyden L.locus w.1 w.2 = 0} := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨hrange ▸ mem_range_self u.proj, ?_⟩
    have hmetric := manifold_metric_eq_coordinate_metric he hemb u.proj u.2
    rw [hrange] at hmetric
    exact hmetric ▸ hu
  · rintro ⟨hw, hk⟩
    have horbit := (torus_locus_metric_zero_iff L hw).mp hk
    obtain ⟨x, hx⟩ := hrange.symm ▸ hw
    have hF : DifferentiableOn ℂ (exponentialOrbit w.1 w.2) (disk 1) := by
      intro z hz
      apply differentiableWithinAt_pi.mpr
      intro j
      unfold exponentialOrbit
      fun_prop
    have hmap : MapsTo (exponentialOrbit w.1 w.2) (disk 1) (range e) :=
      fun z _ => hrange.symm ▸ horbit z
    obtain ⟨v, hv⟩ := ambient_curve_tangent_in_range he hemb x hF hmap
      ((exponentialOrbit_at_zero w.1 w.2).trans hx.symm)
      (hasDerivAt_pi.mpr (exponentialOrbit_hasDerivAt hw.1))
    let u : TangentBundle 𝓘(ℂ, E) M := ⟨x, v⟩
    have hcoord : tangentCoordinates e u = w := Prod.ext hx hv
    refine ⟨u, ?_, hcoord⟩
    change manifoldKobayashiRoyden x v = 0
    rw [manifold_metric_eq_coordinate_metric he hemb, hrange]
    erw [hv, hx]
    exact hk

/-- Exact algebraicity in ambient tangent coordinates, including the converse:
every point of the finite polynomial zero locus is an intrinsic zero direction. -/
theorem torus_manifold_null_image_eq_zeroLocus {N : ℕ} (L : TorusEquations N)
    {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (hrange : range e = L.locus) :
    (fun w : TangentBundle 𝓘(ℂ, E) M =>
      torusJetCoordinates (tangentCoordinates e w).1 (tangentCoordinates e w).2) ''
        manifoldNullDirections = MvPolynomial.zeroLocus ℂ L.nullIdeal := by
  ext a
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (torus_manifold_null_polynomial_criterion L he hemb hrange w).mp hw
  · intro ha
    obtain ⟨x, v, hx, hk, hcoord⟩ := torus_null_zeroLocus_reconstruction L ha
    have hmem : (x, v) ∈ tangentCoordinates (E := E) e '' manifoldNullDirections := by
      rw [torus_manifold_null_tangent_image L he hemb hrange]
      exact ⟨hx, hk⟩
    obtain ⟨w, hw, hwcoord⟩ := hmem
    refine ⟨w, hw, ?_⟩
    exact (congrArg (fun b => torusJetCoordinates b.1 b.2) hwcoord).trans hcoord

end ModifiedCartan
