import ModifiedCartan.FivePhiSign
import ModifiedCartan.FiveMajorant
import ModifiedCartan.GaussianContour

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

def fiveA (n : ℝ) (z : ℂ) : ℂ := 2 * (n : ℂ) * Complex.exp ((n : ℂ) * fiveL z)

def fivea (n : ℝ) (z : ℂ) : ℂ := gaussianTransition n (fivePhi z)

theorem fiveA_unit {n : ℝ} (hn : 0 < n) : IsHolomorphicUnit (fiveA n) (disk 1) := by
  refine ⟨?_, ?_⟩
  · exact ((fiveL_differentiable.const_mul (n : ℂ)).cexp).const_mul (2 * (n : ℂ))
  · intro z _
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hn.ne')) (Complex.exp_ne_zero _)

theorem fivea_differentiable (n : ℝ) : DifferentiableOn ℂ (fivea n) (disk 1) := by
  exact (gaussianTransition_entire n).comp_differentiableOn fivePhi_differentiable

theorem fiveA_norm {n : ℝ} (hn : 0 ≤ n) (z : ℂ) :
    ‖fiveA n z‖ = 2 * n * Real.exp (n * (fiveL z).re) := by
  simp [fiveA, norm_mul, Complex.norm_exp, Complex.mul_re, abs_of_nonneg hn]

theorem fivea_norm_bound {n : ℝ} (hn : 0 < n) {z : ℂ} (hz : z ∈ disk 1) :
    ‖fivea n z‖ ≤ (3 / 2) * Real.exp (n * (fiveL z).re) := by
  have hgap := five_majorant_positive_gap hz
  have hre : (fivePhi z ^ 2).re = (fivePhi z).re ^ 2 - (fivePhi z).im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have he : Real.exp (-n * ((fivePhi z).re ^ 2 - (fivePhi z).im ^ 2)) ≤
      Real.exp (n * (fiveL z).re) := by
    rw [← hre]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hgap.le hn.le]
  change ‖gaussianTransition n (fivePhi z)‖ ≤ _
  by_cases hx : z.re ≤ 0
  · have hh := gaussianTransition_left_bound hn ((fivePhi_re_nonpos_iff hz).mpr hx)
    nlinarith [Real.exp_pos (n * (fiveL z).re)]
  · have hu := fiveL_re_pos_right hz (le_of_not_ge hx)
    have hone : 1 ≤ Real.exp (n * (fiveL z).re) := Real.one_le_exp_iff.mpr (mul_nonneg hn.le hu.le)
    have hh := gaussianTransition_right_bound hn
      ((fivePhi_re_nonneg_iff hz).mpr (le_of_not_ge hx))
    nlinarith

/-- The exact uniform bound 3/(4n) from the manuscript's counterexample. -/
theorem fivea_div_fiveA_bound {n : ℝ} (hn : 0 < n) {z : ℂ} (hz : z ∈ disk 1) :
    ‖fivea n z / fiveA n z‖ ≤ 3 / (4 * n) := by
  rw [norm_div, fiveA_norm hn.le]
  apply (div_le_iff₀ (by positivity : 0 < 2 * n * Real.exp (n * (fiveL z).re))).mpr
  have he : 3 / (4 * n) * (2 * n * Real.exp (n * (fiveL z).re)) =
      (3 / 2) * Real.exp (n * (fiveL z).re) := by field_simp; ring
  rw [he]
  exact fivea_norm_bound hn hz

theorem fivea_sub_fiveA_unit {n : ℝ} (hn : 1 ≤ n) :
    IsHolomorphicUnit (fun z => fivea n z - fiveA n z) (disk 1) := by
  have hn0 : 0 < n := by linarith
  refine ⟨(fivea_differentiable n).sub (fiveA_unit hn0).1, ?_⟩
  intro z hz he
  have heq : fivea n z = fiveA n z := sub_eq_zero.mp he
  have hb := fivea_div_fiveA_bound hn0 hz
  rw [heq, div_self ((fiveA_unit hn0).2 z hz), norm_one] at hb
  have hn4 : 0 < 4 * n := by positivity
  have hh := (le_div_iff₀ hn4).mp hb
  linarith

theorem fivea_complement (n : ℝ) (z : ℂ) : fivea n z + fivea n (-z) = 1 := by
  simpa only [fivea, fivePhi_odd] using gaussianTransition_symmetry n (fivePhi z)

theorem fivea_zero (n : ℝ) : fivea n 0 = 1 / 2 := by
  simp [fivea, fivePhi_zero, gaussianTransition_zero]

theorem fiveA_zero (n : ℝ) : fiveA n 0 = 2 * (n : ℂ) * Complex.exp ((n : ℂ) / 2) := by
  simp [fiveA, fiveL_zero, div_eq_mul_inv]

end ModifiedCartan
