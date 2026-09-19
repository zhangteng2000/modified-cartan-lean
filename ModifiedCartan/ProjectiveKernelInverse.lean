import ModifiedCartan.ProjectiveClass
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

/-- A total extension of the actual inverse on the compact projective image. -/
def projectiveKernelInverse {p : ℕ} (base : Fin p) (M : Fin p → Fin p → ℂ) : ℙ ℂ (Fin p → ℂ) := by
  classical
  exact if h : ∃ q : ℙ ℂ (Fin p → ℂ), projectiveKernel q = M then Classical.choose h
  else projectivePoint base (fun _ => 1)

theorem projectiveKernelInverse_leftInverse {p : ℕ} (base : Fin p)
    (q : ℙ ℂ (Fin p → ℂ)) : projectiveKernelInverse base (projectiveKernel q) = q := by
  unfold projectiveKernelInverse
  split_ifs with h
  · exact projectiveKernel_injective p (Classical.choose_spec h)
  · exact (h ⟨q, rfl⟩).elim

theorem projectiveKernelInverse_continuousOn {p : ℕ} (base : Fin p) :
    ContinuousOn (projectiveKernelInverse base) (range (projectiveKernel (p := p))) := by
  let e := ((projectiveKernel_continuous p).isClosedEmbedding (projectiveKernel_injective p)).isEmbedding.toHomeomorph
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (range (projectiveKernel (p := p))).domRestrict (projectiveKernelInverse base) = e.symm := by
    funext M
    obtain ⟨q, hq⟩ := M.property
    have hM : M = e q := Subtype.ext hq.symm
    rw [hM]
    change projectiveKernelInverse base (projectiveKernel q) = e.symm (e q)
    rw [e.symm_apply_apply]
    exact projectiveKernelInverse_leftInverse base q
  rw [he]
  exact e.symm.continuous

/-- Matrix-coordinate convergence with its limit in the compact projective
image lifts to convergence in the true projective uniformity. -/
theorem projectiveKernel_lift_convergence {p : ℕ} (base : Fin p)
    {F : ℕ → ℂ → ℙ ℂ (Fin p → ℂ)} {H : ℂ → Fin p → Fin p → ℂ} {U : Set ℂ}
    (hH : ContinuousOn H U) (hmap : MapsTo H U (range (projectiveKernel (p := p))))
    (hlim : TendstoLocallyUniformlyOn (fun n z => projectiveKernel (F n z)) H atTop U) :
    ∃ G : ℂ → ℙ ℂ (Fin p → ℂ), ContinuousOn G U ∧
      (∀ z ∈ U, projectiveKernel (G z) = H z) ∧
      TendstoLocallyUniformlyOn F G atTop U := by
  let G : ℂ → ℙ ℂ (Fin p → ℂ) := fun z => projectiveKernelInverse base (H z)
  have hcompact := isCompact_range (projectiveKernel_continuous p)
  have hcont := projectiveKernelInverse_continuousOn base
  refine ⟨G, hcont.comp hH hmap, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq⟩ := hmap hz
    dsimp [G]
    rw [← hq, projectiveKernelInverse_leftInverse]
  · have hh := (hcompact.uniformContinuousOn_of_continuous hcont).comp_tendstoLocallyUniformlyOn
      hlim hmap (Eventually.of_forall fun n z _ => mem_range_self (F n z))
    exact hh.congr (fun n z _ => projectiveKernelInverse_leftInverse base (F n z))

theorem projectiveHyperplane_isClosed (p : ℕ) : IsClosed (projectiveHyperplane p) := by
  apply (projective_mk_isQuotientMap p).isCoinducing.isClosed_preimage.mp
  have he : (Projectivization.mk' ℂ : {x : Fin p → ℂ // x ≠ 0} → ℙ ℂ (Fin p → ℂ)) ⁻¹' projectiveHyperplane p =
      {x : {x : Fin p → ℂ // x ≠ 0} | ∑ j, x.val j = 0} := by
    ext x
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) x.val x.property
    change (∑ j, (Projectivization.mk ℂ x.val x.property).rep j = 0) ↔ (∑ j, x.val j = 0)
    rw [← hc]
    simp only [Pi.smul_apply, ← Finset.smul_sum, smul_eq_zero_iff_eq]
  rw [he]
  exact isClosed_eq (continuous_finsetSum _ (fun j _ =>
    (continuous_apply j).comp continuous_subtype_val)) continuous_const

end ModifiedCartan
