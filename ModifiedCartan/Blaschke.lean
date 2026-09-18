import ModifiedCartan.LogPoisson
import Mathlib.Analysis.Complex.CanonicalDecomposition

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Metric Set
namespace ModifiedCartan

/-- Blaschke factor in the manuscript convention (the inverse of mathlib's canonical factor). -/
def blaschkeFactor (R : ℝ) (a z : ℂ) : ℂ :=
  (R : ℂ) * (z - a) / (((R ^ 2 : ℝ) : ℂ) - conj a * z)

theorem blaschkeFactor_analytic {R : ℝ} (hR : 0 < R) {a : ℂ} (ha : ‖a‖ < R) :
    AnalyticOnNhd ℂ (blaschkeFactor R a) (closedBall (0 : ℂ) R) := by
  intro z hz
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  exact blaschke_numerator_ne_zero hR ha (by simpa using hz)

theorem blaschkeFactor_norm_le_one {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) : ‖blaschkeFactor R a z‖ ≤ 1 := by
  have hd := blaschke_numerator_ne_zero hR ha hz
  have hi := blaschke_norm_identity R a z
  have hp : 0 ≤ (R ^ 2 - ‖a‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) :=
    mul_nonneg (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  have hn : R * ‖z - a‖ ≤ ‖((R ^ 2 : ℝ) : ℂ) - conj a * z‖ := by
    nlinarith [norm_nonneg (((R ^ 2 : ℝ) : ℂ) - conj a * z), norm_nonneg (z - a)]
  simp only [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact (div_le_one (norm_pos_iff.mpr hd)).mpr hn

theorem blaschkeFactor_norm_lt_one {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ < R) : ‖blaschkeFactor R a z‖ < 1 := by
  have hd := blaschke_numerator_ne_zero hR ha hz.le
  have hi := blaschke_norm_identity R a z
  have hp : 0 < (R ^ 2 - ‖a‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  have hn : R * ‖z - a‖ < ‖((R ^ 2 : ℝ) : ℂ) - conj a * z‖ := by
    nlinarith [norm_nonneg (((R ^ 2 : ℝ) : ℂ) - conj a * z), norm_nonneg (z - a)]
  simp only [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  exact (div_lt_one (norm_pos_iff.mpr hd)).mpr hn

theorem blaschkeFactor_norm_on_circle {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ = R) : ‖blaschkeFactor R a z‖ = 1 := by
  have hd := blaschke_numerator_ne_zero hR ha hz.le
  have hi := blaschke_norm_identity R a z
  rw [hz, sub_self, mul_zero] at hi
  have hn : R * ‖z - a‖ = ‖((R ^ 2 : ℝ) : ℂ) - conj a * z‖ := by
    apply (sq_eq_sq₀ (mul_nonneg hR.le (norm_nonneg _)) (norm_nonneg _)).mp
    nlinarith only [hi]
  simp only [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  rw [hn, div_self (norm_ne_zero_iff.mpr hd)]

/-- Uniform strict contraction when both the zero and the evaluation point stay
in fixed smaller closed disks. The resulting q depends only on the radii. -/
theorem blaschkeFactor_uniform_bound {R A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAR : A < R) (hBR : B < R) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ a z : ℂ, ‖a‖ ≤ A → ‖z‖ ≤ B →
      ‖blaschkeFactor R a z‖ ≤ q := by
  have hR : 0 < R := lt_of_le_of_lt hA hAR
  let K := closedBall (0 : ℂ) A ×ˢ closedBall (0 : ℂ) B
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hne : K.Nonempty := ⟨(0, 0), by simp [K, hA, hB]⟩
  have hc : ContinuousOn (fun v : ℂ × ℂ => ‖blaschkeFactor R v.1 v.2‖) K := by
    apply ContinuousOn.norm
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro v hv
    exact blaschke_numerator_ne_zero hR (lt_of_le_of_lt (by simpa [K] using hv.1) hAR)
      ((show ‖v.2‖ ≤ B by simpa [K] using hv.2).trans hBR.le)
  obtain ⟨v, hv, hmax⟩ := hK.exists_isMaxOn hne hc
  refine ⟨‖blaschkeFactor R v.1 v.2‖, norm_nonneg _, ?_, ?_⟩
  · exact blaschkeFactor_norm_lt_one hR
      (lt_of_le_of_lt (by simpa [K] using hv.1) hAR)
      (lt_of_le_of_lt (by simpa [K] using hv.2) hBR)
  · intro a z ha hz
    exact hmax (show (a, z) ∈ K by simpa [K] using And.intro ha hz)

theorem blaschkeFactor_radial_lower {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    {a z : ℂ} (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) :
    |‖z‖ - ‖a‖| / 2 ≤ ‖blaschkeFactor R a z‖ := by
  have hd := blaschke_numerator_ne_zero hR ha hz
  have hden : ‖((R ^ 2 : ℝ) : ℂ) - conj a * z‖ ≤ 2 * R ^ 2 := by
    calc
      _ ≤ ‖((R ^ 2 : ℝ) : ℂ)‖ + ‖conj a * z‖ := norm_sub_le _ _
      _ = R ^ 2 + ‖a‖ * ‖z‖ := by simp
      _ ≤ _ := by nlinarith [mul_le_mul ha.le hz (norm_nonneg z) hR.le]
  have hr := abs_norm_sub_norm_le z a
  have hn : 0 ≤ ‖blaschkeFactor R a z‖ := norm_nonneg _
  have he : ‖blaschkeFactor R a z‖ * ‖((R ^ 2 : ℝ) : ℂ) - conj a * z‖ =
      R * ‖z - a‖ := by
    simp only [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hd)
  have hi := mul_le_mul_of_nonneg_left hden hn
  have hR2 : R ^ 2 ≤ R := by nlinarith
  have hi2 := mul_le_mul_of_nonneg_left hR2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn)
  have hmain : ‖z - a‖ ≤ 2 * ‖blaschkeFactor R a z‖ := by nlinarith
  linarith

end ModifiedCartan
