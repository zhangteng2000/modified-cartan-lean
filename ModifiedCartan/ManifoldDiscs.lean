import ModifiedCartan.ImmersionDifferential
import ModifiedCartan.Kobayashi
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
set_option autoImplicit false
open Set Filter Topology Manifold
open scoped Manifold ContDiff ENNReal
namespace ModifiedCartan

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) 1 M]

/-- Analytic discs with the intrinsic manifold differential. Tangent fibers are
represented in the model space, as in mathlib's `TangentSpace`. -/
structure ManifoldTangentDisc (x : M) (v : TangentSpace 𝓘(ℂ, E) x) (t : ℝ) where
  map : ℂ → M
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, E) map (disk 1)
  center : map 0 = x
  tangent : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, E) map 0 (1 : ℂ) = (t : ℂ) • v

def manifoldKobayashiRoyden (x : M) (v : TangentSpace 𝓘(ℂ, E) x) : ℝ≥0∞ :=
  sInf {c | ∃ t : ℝ, 0 < t ∧ c = ENNReal.ofReal (1 / t) ∧
    Nonempty (ManifoldTangentDisc x v t)}

theorem manifold_disc_embedding {N : ℕ} {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    {x : M} {v : TangentSpace 𝓘(ℂ, E) x} {t : ℝ}
    (F : ManifoldTangentDisc x v t) :
    Nonempty (TangentDisc (range e) (e x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e x v) t) := by
  have hF : ∀ z ∈ disk 1, MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) F.map z := by
    intro z hz
    exact (F.holomorphic z hz).mdifferentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have he' := he.contMDiff.mdifferentiable (by norm_num)
  have hc : ∀ z ∈ disk 1, DifferentiableAt ℂ (e ∘ F.map) z := by
    intro z hz
    exact ((he' (F.map z)).comp z (hF z hz)).differentiableAt
  have h0 : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hd : deriv (e ∘ F.map) 0 = (t : ℂ) •
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e x v) := by
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv]
    erw [mfderiv_comp_apply 0 (he' (F.map 0)) (hF 0 h0) (1 : ℂ), F.tangent, F.center,
      map_smul]
  refine ⟨{ map := e ∘ F.map
            holomorphic := ?_
            mapsTo := fun z _ => mem_range_self _
            center := by simp [Function.comp_def, F.center]
            tangent := ?_ }⟩
  · intro j z hz
    exact (differentiableAt_pi.mp (hc z hz) j).differentiableWithinAt
  · intro j
    have h := (hasDerivAt_pi.mp ((hc 0 h0).hasDerivAt)) j
    have hdj : deriv (e ∘ F.map) 0 j = (t : ℂ) *
        (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e x v) j := congrFun hd j
    rw [hdj] at h
    exact h

theorem immersion_holomorphic_lift {N : ℕ} {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (x : M) {F : ℂ → Fin N → ℂ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hmap : MapsTo F (disk 1) (range e)) :
    ∃ g : ℂ → M, (∀ z ∈ disk 1, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) 1 g z) ∧
      EqOn (e ∘ g) F (disk 1) := by
  classical
  let g : ℂ → M := fun z => if hz : z ∈ disk 1 then Classical.choose (hmap hz) else x
  have hval : ∀ z ∈ disk 1, e (g z) = F z := by
    intro z hz
    simp only [g, dite_eq_left hz]
    exact Classical.choose_spec (hmap hz)
  have heq : ∀ z ∈ disk 1, e ∘ g =ᶠ[𝓝 z] F := by
    intro z hz
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact hval y hy
  refine ⟨g, ?_, hval⟩
  intro z hz
  have hc : ContDiffAt ℂ 1 (e ∘ g) z :=
    ((hF.contDiffOn Metric.isOpen_ball).contDiffAt (Metric.isOpen_ball.mem_nhds hz)).congr_of_eventuallyEq
      (heq z hz)
  exact (ContMDiffAt.iff_comp_isImmersionAt (he.isImmersionAt (g z))).mpr
    ⟨hemb.isInducing.continuousAt_iff.mpr hc.continuousAt, hc.contMDiffAt⟩

theorem coordinate_disc_lift {N : ℕ} {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e)
    {x : M} {v : TangentSpace 𝓘(ℂ, E) x} {t : ℝ}
    (F : TangentDisc (range e) (e x) (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e x v) t) :
    Nonempty (ManifoldTangentDisc x v t) := by
  have hF : DifferentiableOn ℂ F.map (disk 1) := fun z hz =>
    differentiableWithinAt_pi.mpr (fun j => F.holomorphic j z hz)
  obtain ⟨g, hg, hval⟩ := immersion_holomorphic_lift he hemb x hF F.mapsTo
  have heq : ∀ z ∈ disk 1, e ∘ g =ᶠ[𝓝 z] F.map := by
    intro z hz
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact hval hy
  have h0 : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hg0 : g 0 = x := hemb.injective ((hval h0).trans F.center)
  refine ⟨{ map := g
            holomorphic := fun z hz => (hg z hz).mdifferentiableAt (by norm_num)
              |>.mdifferentiableWithinAt
            center := hg0
            tangent := ?_ }⟩
  apply immersion_mfderiv_injective (he.isImmersionAt x)
  have hchain := mfderiv_comp_apply 0
    ((he.contMDiff.mdifferentiable (by norm_num)) (g 0))
    ((hg 0 h0).mdifferentiableAt (by norm_num)) (1 : ℂ)
  rw [hg0] at hchain
  have hd : HasDerivAt F.map ((t : ℂ) •
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e x v)) 0 :=
    hasDerivAt_pi.mpr F.tangent
  erw [map_smul, ← hchain, (heq 0 h0).mfderiv_eq, mfderiv_eq_fderiv,
    fderiv_apply_one_eq_deriv (𝕜 := ℂ) (f := F.map) (x := 0), hd.deriv]

theorem manifold_metric_eq_coordinate_metric {N : ℕ} {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e)
    (x : M) (v : TangentSpace 𝓘(ℂ, E) x) :
    manifoldKobayashiRoyden x v = kobayashiRoyden (range e) (e x)
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e x v) := by
  unfold manifoldKobayashiRoyden kobayashiRoyden
  congr 1
  ext c
  constructor
  · rintro ⟨t, ht, hc, ⟨F⟩⟩
    exact ⟨t, ht, hc, manifold_disc_embedding he F⟩
  · rintro ⟨t, ht, hc, ⟨F⟩⟩
    exact ⟨t, ht, hc, coordinate_disc_lift he hemb F⟩

/-- The velocity of any ambient analytic curve in an embedded manifold belongs
to the image of the intrinsic tangent space. -/
theorem ambient_curve_tangent_in_range {N : ℕ} {e : M → Fin N → ℂ}
    (he : IsImmersion 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) 1 e)
    (hemb : Topology.IsEmbedding e) (x : M) {F : ℂ → Fin N → ℂ} {v : Fin N → ℂ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hmap : MapsTo F (disk 1) (range e))
    (hcenter : F 0 = e x) (hd : HasDerivAt F v 0) :
    ∃ u : TangentSpace 𝓘(ℂ, E) x, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin N → ℂ) e x u = v := by
  obtain ⟨g, hg, hval⟩ := immersion_holomorphic_lift he hemb x hF hmap
  have h0 : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hg0 : g 0 = x := hemb.injective ((hval h0).trans hcenter)
  have heq : e ∘ g =ᶠ[𝓝 (0 : ℂ)] F := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with z hz
    exact hval hz
  refine ⟨mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, E) g 0 (1 : ℂ), ?_⟩
  have hchain := mfderiv_comp_apply 0
    ((he.contMDiff.mdifferentiable (by norm_num)) (g 0))
    ((hg 0 h0).mdifferentiableAt (by norm_num)) (1 : ℂ)
  rw [hg0] at hchain
  erw [← hchain, heq.mfderiv_eq, mfderiv_eq_fderiv,
    fderiv_apply_one_eq_deriv (𝕜 := ℂ) (f := F) (x := 0), hd.deriv]

end ModifiedCartan
