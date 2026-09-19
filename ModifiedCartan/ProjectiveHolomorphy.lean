import ModifiedCartan.ProjectiveClass
import ModifiedCartan.ProjectiveManifold

noncomputable section
set_option autoImplicit false
open Set Topology Manifold
open scoped LinearAlgebra.Projectivization Manifold ContDiff
namespace ModifiedCartan

variable {p : ℕ} (base : Fin p) [Nonempty (ProjectiveX p)]

/-- Agreement between affine-coordinate holomorphy and the actual complex
manifold structure already constructed on X_p. -/
theorem projectiveX_holomorphic_iff {F : ℂ → ProjectiveX p} {U : Set ℂ} (hU : IsOpen U) :
    letI := projectiveXChartedSpace base
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, normalizedDirectionSubspace base) F U ↔
      ProjectiveHolomorphicOn (fun z => (F z).val) U := by
  letI := projectiveXChartedSpace base
  letI := projectiveX_isManifold base
  have he := projectiveXNormalize_isImmersion base
  have hemb := projectiveXNormalize_isEmbedding base
  constructor
  · intro hF
    have hd : DifferentiableOn ℂ (fun z => projectiveXNormalize base (F z)) U := by
      rw [← mdifferentiableOn_iff_differentiableOn]
      exact (he.contMDiff.mdifferentiable (by norm_num)).comp_mdifferentiableOn hF
    have hj (j : Fin p) : DifferentiableOn ℂ (fun z => projectiveXNormalize base (F z) j) U :=
      (differentiableOn_pi.mp hd) j
    refine ⟨continuous_subtype_val.comp_continuousOn hF.continuousOn, ?_⟩
    intro k j
    have hn : ∀ z ∈ U, projectiveXNormalize base (F z) k ≠ 0 := by
      intro z _
      exact div_ne_zero ((F z).property.1 k) ((F z).property.1 base)
    have hquot := ((hj j).div (hj k) hn).mono
      (show U ∩ (fun z => (F z).val) ⁻¹' projectiveChartSet k ⊆ U from inter_subset_left)
    apply hquot.congr
    intro z hz
    change (F z).val.rep j / (F z).val.rep k =
      ((F z).val.rep j / (F z).val.rep base) / ((F z).val.rep k / (F z).val.rep base)
    field_simp [(F z).property.1 base, (F z).property.1 k]
  · intro hF z hz
    have hd : DifferentiableOn ℂ (fun z => projectiveXNormalize base (F z)) U := by
      apply differentiableOn_pi.mpr
      intro j
      exact (hF.2 base j).mono (fun z hz => ⟨hz, (F z).property.1 base⟩)
    have hc : ContDiffAt ℂ 1 (projectiveXNormalize base ∘ F) z :=
      (hd.contDiffOn hU).contDiffAt (hU.mem_nhds hz)
    have hm : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, normalizedDirectionSubspace base) 1 F z :=
      (ContMDiffAt.iff_comp_isImmersionAt (he.isImmersionAt (F z))).mpr
        ⟨hemb.isInducing.continuousAt_iff.mpr hc.continuousAt, hc.contMDiffAt⟩
    exact (hm.mdifferentiableAt (by norm_num)).mdifferentiableWithinAt

end ModifiedCartan
