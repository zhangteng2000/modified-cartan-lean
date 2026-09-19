import ModifiedCartan.ProjectiveKernel
import Mathlib.Topology.UniformSpace.OfCompactT2
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option autoImplicit false
open Set Topology Metric
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

theorem projective_sphere_nonzero {p : ℕ} (x : sphere (0 : Fin p → ℂ) 1) : x.val ≠ 0 := by
  intro h
  have hh := x.property
  simp [h] at hh

def projectiveSphereMap (p : ℕ) (x : sphere (0 : Fin p → ℂ) 1) : ℙ ℂ (Fin p → ℂ) :=
  Projectivization.mk ℂ x.val (projective_sphere_nonzero x)

theorem projectiveSphereMap_continuous (p : ℕ) : Continuous (projectiveSphereMap p) := by
  exact (projective_mk_isQuotientMap p).continuous.comp
    (continuous_subtype_val.subtype_mk (fun x => projective_sphere_nonzero x))

theorem projectiveSphereMap_surjective (p : ℕ) : Function.Surjective (projectiveSphereMap p) := by
  intro q
  have hn : ‖q.rep‖ ≠ 0 := norm_ne_zero_iff.mpr q.rep_nonzero
  let c : ℂ := (‖q.rep‖⁻¹ : ℝ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hn)
  have hnorm : ‖c • q.rep‖ = 1 := by
    rw [norm_smul]
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hn
  let x : sphere (0 : Fin p → ℂ) 1 := ⟨c • q.rep, by simpa using hnorm⟩
  refine ⟨x, ?_⟩
  apply projectiveKernel_injective p
  change projectiveKernelCoordinates (Projectivization.mk ℂ x.val _).rep =
    projectiveKernelCoordinates q.rep
  rw [projectiveKernelCoordinates_mk]
  exact projectiveKernelCoordinates_smul q.rep hc

instance projectivizationCompactSpace (p : ℕ) : CompactSpace (ℙ ℂ (Fin p → ℂ)) := by
  letI : CompactSpace (sphere (0 : Fin p → ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Fin p → ℂ) 1)
  apply isCompact_univ_iff.mp
  rw [← (projectiveSphereMap_surjective p).range_eq]
  exact isCompact_range (projectiveSphereMap_continuous p)

/-- The unique uniformity compatible with the genuine compact Hausdorff
quotient topology on complex projective space. -/
instance projectivizationUniformSpace (p : ℕ) : UniformSpace (ℙ ℂ (Fin p → ℂ)) :=
  uniformSpaceOfCompactR1

end ModifiedCartan
