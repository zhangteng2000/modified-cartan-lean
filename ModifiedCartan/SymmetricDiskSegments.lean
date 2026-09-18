import ModifiedCartan.DiskAutomorphisms
import ModifiedCartan.HyperbolicDiameter
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Complex Metric Real Set
namespace ModifiedCartan

def symmetricPseudodistance (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

theorem symmetricPseudodistance_continuous : Continuous symmetricPseudodistance := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  positivity

theorem symmetricPseudodistance_zero : symmetricPseudodistance 0 = 0 := by simp [symmetricPseudodistance]

theorem symmetricPseudodistance_sharpRadius : symmetricPseudodistance sharpRadius = 1 / 2 := by
  unfold symmetricPseudodistance
  rw [sharpRadius_quadratic]
  field_simp [sharpRadius_pos.ne']
  ring

theorem exists_symmetric_radius {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hrq : r ≤ symmetricPseudodistance q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ q ∧ symmetricPseudodistance t = r := by
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc hq symmetricPseudodistance_continuous.continuousOn
    (show r ∈ Icc (symmetricPseudodistance 0) (symmetricPseudodistance q) by
      rw [symmetricPseudodistance_zero]; exact ⟨hr, hrq⟩)
  exact ⟨t, ht.1, ht.2, htr⟩

theorem exists_uniform_symmetric_radius {r : ℝ} (hr : 0 ≤ r) (hrh : r < 1 / 2) :
    ∃ q : ℝ, 0 < q ∧ q < sharpRadius ∧ r < symmetricPseudodistance q := by
  obtain ⟨q, hq0, hqr, hqe⟩ := exists_symmetric_radius sharpRadius_pos.le
    (show 0 ≤ (r + 1 / 2) / 2 by linarith)
    (show (r + 1 / 2) / 2 ≤ symmetricPseudodistance sharpRadius by
      rw [symmetricPseudodistance_sharpRadius]; linarith)
  refine ⟨q, lt_of_le_of_ne hq0 ?_, lt_of_le_of_ne hqr ?_, ?_⟩
  · intro hzero
    rw [← hzero, symmetricPseudodistance_zero] at hqe
    linarith
  · intro he
    rw [he, symmetricPseudodistance_sharpRadius] at hqe
    linarith
  · rw [hqe]
    linarith

theorem diskAutomorphism_real_opposite (t : ℝ) :
    diskAutomorphism (t : ℂ) (-t : ℝ) = (symmetricPseudodistance t : ℂ) := by
  simp only [diskAutomorphism, conj_ofReal, ofReal_neg, mul_neg, sub_neg_eq_add,
    symmetricPseudodistance, ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_add, ofReal_one, ofReal_pow]
  congr 1 <;> ring

/-- A concrete disk automorphism parameterizing the symmetric endpoint segment. -/
def diskSegmentMap (a ξ : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  diskAutomorphism a (ξ * diskAutomorphism (t : ℂ) (-z))

theorem diskSegmentMap_mem_disk {a ξ z : ℂ} {t : ℝ}
    (ha : ‖a‖ < 1) (hξ : ‖ξ‖ = 1) (ht : |t| < 1) (hz : z ∈ disk 1) :
    diskSegmentMap a ξ t z ∈ disk 1 := by
  apply diskAutomorphism_mem_disk ha
  have htn : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hnz : -z ∈ disk 1 := by simpa [disk] using hz
  have hh := diskAutomorphism_mem_disk htn hnz
  simpa only [disk, mem_ball, dist_zero_right, norm_mul, hξ, one_mul] using hh

theorem diskSegmentMap_analytic {a ξ : ℂ} {t : ℝ}
    (ha : ‖a‖ < 1) (hξ : ‖ξ‖ = 1) (ht : |t| < 1) :
    AnalyticOnNhd ℂ (diskSegmentMap a ξ t) (disk 1) := by
  intro z hz
  have htn : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hnz : -z ∈ disk 1 := by simpa [disk] using hz
  have hi := (diskAutomorphism_analytic htn (-z) (ball_subset_closedBall hnz)).comp
    (show AnalyticAt ℂ (fun z : ℂ => -z) z by fun_prop)
  have hmid : ξ * diskAutomorphism (t : ℂ) (-z) ∈ disk 1 := by
    have hh := diskAutomorphism_mem_disk htn hnz
    simpa only [disk, mem_ball, dist_zero_right, norm_mul, hξ, one_mul] using hh
  have hmul : AnalyticAt ℂ (fun w => ξ * diskAutomorphism (t : ℂ) (-w)) z := by
    simpa only [Function.comp_def, Pi.mul_def] using (analyticAt_const.mul hi)
  change AnalyticAt ℂ (fun w => diskAutomorphism a (ξ * diskAutomorphism (t : ℂ) (-w))) z
  exact AnalyticAt.comp (f := fun w => ξ * diskAutomorphism (t : ℂ) (-w)) (x := z)
    (diskAutomorphism_analytic ha _ (ball_subset_closedBall hmid)) hmul

theorem diskSegmentMap_left (a ξ : ℂ) (t : ℝ) : diskSegmentMap a ξ t ((-t : ℝ) : ℂ) = a := by
  simp [diskSegmentMap, diskAutomorphism_self, diskAutomorphism_zero]

theorem diskSegmentMap_right {a b ξ : ℂ} {t : ℝ} (ha : ‖a‖ < 1) (hb : b ∈ disk 1)
    (he : ξ * (symmetricPseudodistance t : ℂ) = diskAutomorphism a b) :
    diskSegmentMap a ξ t (t : ℂ) = b := by
  unfold diskSegmentMap
  rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by simp, diskAutomorphism_real_opposite, he,
    diskAutomorphism_involutive ha hb]

/-- Construct actual symmetric endpoint coordinates, including coincident endpoints. -/
theorem exists_diskSegmentMap {a b : ℂ} {q : ℝ}
    (ha : a ∈ disk 1) (hb : b ∈ disk 1) (hq : 0 ≤ q)
    (hab : ‖diskAutomorphism a b‖ ≤ symmetricPseudodistance q) :
    ∃ t : ℝ, ∃ ξ : ℂ, 0 ≤ t ∧ t ≤ q ∧ ‖ξ‖ = 1 ∧
      diskSegmentMap a ξ t ((-t : ℝ) : ℂ) = a ∧ diskSegmentMap a ξ t (t : ℂ) = b := by
  have han : ‖a‖ < 1 := by simpa [disk] using ha
  by_cases hnz : diskAutomorphism a b = 0
  · have he : a = b := by
      have hh := diskAutomorphism_involutive han hb
      simpa only [hnz, diskAutomorphism_zero] using hh
    refine ⟨0, 1, le_rfl, hq, norm_one, diskSegmentMap_left _ _ _, ?_⟩
    simpa [diskSegmentMap, diskAutomorphism_zero] using he
  · let r := ‖diskAutomorphism a b‖
    have hr : 0 < r := norm_pos_iff.mpr hnz
    obtain ⟨t, ht, htq, htr⟩ := exists_symmetric_radius hq hr.le hab
    let ξ := diskAutomorphism a b / (r : ℂ)
    have hξ : ‖ξ‖ = 1 := by
      dsimp [ξ]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact div_self hr.ne'
    refine ⟨t, ξ, ht, htq, hξ, diskSegmentMap_left _ _ _, ?_⟩
    apply diskSegmentMap_right han hb
    rw [htr]
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')

end ModifiedCartan
