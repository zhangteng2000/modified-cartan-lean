import ModifiedCartan.ManifoldDiscs
import ModifiedCartan.TorusAlgebraicNull
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
set_option autoImplicit false
open Set Filter Topology Manifold
open scoped Manifold ContDiff ENNReal
namespace ModifiedCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) 1 M]

def tangentCoordinates {N : ℕ} (e : M → Fin N → ℂ)
    (w : TangentBundle 𝓘(ℂ, E) M) : (Fin N → ℂ) × (Fin N → ℂ) :=
  (e w.proj, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e w.proj w.2)

theorem continuous_tangentCoordinates {N : ℕ} {e : M → Fin N → ℂ}
    (he : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e) :
    Continuous (tangentCoordinates (E := E) e) := by
  exact (tangentBundleModelSpaceHomeomorph 𝓘(ℂ, Fin N → ℂ)).continuous.comp
    (he.continuous_tangentMap le_rfl)

def manifoldNullDirections : Set (TangentBundle 𝓘(ℂ, E) M) :=
  {w | manifoldKobayashiRoyden w.proj w.2 = 0}

/-- The intrinsic zero-direction theorem for every embedded complex manifold
whose image is the prescribed closed Laurent locus. -/
theorem torus_manifold_metric_zero_iff {N : ℕ} (L : TorusEquations N)
    {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (hrange : range e = L.locus)
    (x : M) (v : TangentSpace 𝓘(ℂ, E) x) :
    manifoldKobayashiRoyden x v = 0 ↔ ∀ z : ℂ,
      exponentialOrbit (e x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e x v) z ∈ L.locus := by
  rw [manifold_metric_eq_coordinate_metric he hemb, hrange]
  exact torus_locus_metric_zero_iff L (hrange ▸ mem_range_self x)

theorem torus_manifold_nullDirections_isClosed {N : ℕ} (L : TorusEquations N)
    {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (hrange : range e = L.locus) :
    IsClosed (manifoldNullDirections (E := E) (M := M)) := by
  let j : TangentBundle 𝓘(ℂ, E) M → L.locus × (Fin N → ℂ) :=
    fun w => (⟨e w.proj, hrange ▸ mem_range_self w.proj⟩, (tangentCoordinates e w).2)
  have hj : Continuous j := by
    exact ((continuous_tangentCoordinates he.contMDiff).fst.subtype_mk _).prodMk
      (continuous_tangentCoordinates he.contMDiff).snd
  have heq : manifoldNullDirections (E := E) (M := M) = j ⁻¹' L.nullDirections := by
    ext w
    change manifoldKobayashiRoyden w.proj w.2 = 0 ↔
      kobayashiRoyden L.locus (e w.proj)
        (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e w.proj w.2) = 0
    rw [manifold_metric_eq_coordinate_metric he hemb, hrange]
  rw [heq]
  exact (torus_nullDirections_isClosed L).preimage hj

theorem torus_manifold_compact_metric_lower {N : ℕ} (L : TorusEquations N)
    {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (hrange : range e = L.locus)
    {K : Set (TangentBundle 𝓘(ℂ, E) M)} (hK : IsCompact K)
    (hKsub : K ⊆ (manifoldNullDirections (E := E) (M := M))ᶜ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ K, ENNReal.ofReal ε ≤ manifoldKobayashiRoyden w.proj w.2 := by
  have hmetric : ∀ w : TangentBundle 𝓘(ℂ, E) M,
      manifoldKobayashiRoyden w.proj w.2 =
        kobayashiRoyden L.locus (tangentCoordinates e w).1 (tangentCoordinates e w).2 := by
    intro w
    rw [manifold_metric_eq_coordinate_metric he hemb, hrange]
    rfl
  have hsub : ∀ w ∈ tangentCoordinates e '' K,
      w.1 ∈ L.locus ∧ kobayashiRoyden L.locus w.1 w.2 ≠ 0 := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨hrange ▸ mem_range_self w.proj, ?_⟩
    rw [← hmetric w]
    exact hKsub hw
  obtain ⟨ε, hε, hbound⟩ := torus_locus_compact_metric_lower L
    (hK.image (continuous_tangentCoordinates he.contMDiff)) hsub
  refine ⟨ε, hε, fun w hw => ?_⟩
  rw [hmetric w]
  exact hbound _ (mem_image_of_mem _ hw)

theorem torus_manifold_compact_inf_pos {N : ℕ} (L : TorusEquations N)
    {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (hrange : range e = L.locus)
    {K : Set (TangentBundle 𝓘(ℂ, E) M)} (hK : IsCompact K)
    (hKsub : K ⊆ (manifoldNullDirections (E := E) (M := M))ᶜ) :
    0 < sInf ((fun w => manifoldKobayashiRoyden w.proj w.2) '' K) := by
  obtain ⟨ε, hε, hbound⟩ := torus_manifold_compact_metric_lower L he hemb hrange hK hKsub
  apply lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hε)
  apply le_sInf
  rintro _ ⟨w, hw, rfl⟩
  exact hbound w hw

theorem torus_manifold_null_polynomial_criterion {N : ℕ} (L : TorusEquations N)
    {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (hrange : range e = L.locus)
    (w : TangentBundle 𝓘(ℂ, E) M) :
    w ∈ manifoldNullDirections ↔
      torusJetCoordinates (tangentCoordinates e w).1 (tangentCoordinates e w).2 ∈
        MvPolynomial.zeroLocus ℂ L.nullIdeal := by
  change manifoldKobayashiRoyden w.proj w.2 = 0 ↔ _
  rw [manifold_metric_eq_coordinate_metric he hemb, hrange]
  exact torus_metric_zero_iff_polynomial_zeroLocus L (hrange ▸ mem_range_self w.proj)

end ModifiedCartan
