import ModifiedCartan.CauchyBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
set_option autoImplicit false
open Complex Real
namespace ModifiedCartan

theorem circle_distance_real_sq (R A θ : ℝ) :
    ‖circleMap 0 R θ - (A : ℂ)‖ ^ 2 = (R - A) ^ 2 + 2 * R * A * (1 - Real.cos θ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [circleMap, zero_add, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, zero_mul, sub_zero, add_zero, Real.exp_zero, one_mul]
  have htrig : R ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) = R ^ 2 := by
    rw [Real.sin_sq_add_cos_sq, mul_one]
  nlinarith only [htrig]

/-- The uniform angular lower bound when a real pole lies near the circle. -/
theorem circle_distance_angular_lower {R A θ : ℝ} (hR : 0 < R)
    (hA : R / 2 ≤ A) (hθ : |θ| ≤ Real.pi) :
    R / Real.pi * |θ| ≤ ‖circleMap 0 R θ - (A : ℂ)‖ := by
  have hA0 : 0 ≤ A := by linarith
  have hc := Real.cos_le_one_sub_mul_cos_sq hθ
  have hc0 : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
  have hsq := circle_distance_real_sq R A θ
  have hpp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hc' : 2 * θ ^ 2 ≤ Real.pi ^ 2 * (1 - Real.cos θ) := by
    have hh := mul_le_mul_of_nonneg_left hc hpp.le
    field_simp at hh
    nlinarith only [hh]
  have hmul1 := mul_le_mul_of_nonneg_left hA hR.le
  have hmul2 := mul_le_mul_of_nonneg_right (show R ^ 2 ≤ 2 * R * A by nlinarith) hc0
  have hmul3 := mul_le_mul_of_nonneg_left hc' (sq_nonneg R)
  have hmul4 := mul_le_mul_of_nonneg_left hmul2 hpp.le
  have hmul5 := mul_le_mul_of_nonneg_left (show 2 * R * A * (1 - Real.cos θ) ≤
      ‖circleMap 0 R θ - (A : ℂ)‖ ^ 2 by nlinarith only [hsq, sq_nonneg (R - A)]) hpp.le
  have hsqbound : R ^ 2 * θ ^ 2 ≤ Real.pi ^ 2 * ‖circleMap 0 R θ - (A : ℂ)‖ ^ 2 := by
    nlinarith only [hmul3, hmul4, hmul5, mul_nonneg (sq_nonneg R) (sq_nonneg θ)]
  have htarget : (R / Real.pi * |θ|) ^ 2 ≤ ‖circleMap 0 R θ - (A : ℂ)‖ ^ 2 := by
    rw [mul_pow, div_pow, sq_abs]
    calc
      _ = (R ^ 2 * θ ^ 2) / Real.pi ^ 2 := by ring
      _ ≤ _ := (div_le_iff₀ hpp).mpr (by simpa [mul_comm] using hsqbound)
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp htarget

theorem circle_distance_small_pole {R A θ : ℝ} (hR : 0 < R)
    (hA0 : 0 ≤ A) (hA : A ≤ R / 2) :
    R / 2 ≤ ‖circleMap 0 R θ - (A : ℂ)‖ := by
  have hh := norm_sub_norm_le (circleMap 0 R θ) (A : ℂ)
  have he : ‖circleMap 0 R θ‖ = R := by simp [abs_of_pos hR]
  rw [he] at hh
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0] at hh
  linarith

theorem circle_inverse_power_domination {R A θ p : ℝ} (hR : 0 < R)
    (hA : 0 ≤ A) (hp : 0 ≤ p) (hθ : |θ| ≤ Real.pi) (hθ0 : θ ≠ 0) :
    ‖circleMap 0 R θ - (A : ℂ)‖ ^ (-p) ≤
      (R / 2) ^ (-p) + (R / Real.pi) ^ (-p) * |θ| ^ (-p) := by
  by_cases ha : A ≤ R / 2
  · have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R / 2)
      (circle_distance_small_pole (θ := θ) hR hA ha) (neg_nonpos.mpr hp)
    exact hh.trans (le_add_of_nonneg_right (mul_nonneg
      (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (abs_nonneg _) _)))
  · have hlower := circle_distance_angular_lower hR (le_of_not_ge ha) hθ
    have hpos : 0 < R / Real.pi * |θ| := mul_pos (div_pos hR Real.pi_pos) (abs_pos.mpr hθ0)
    have hh := Real.rpow_le_rpow_of_nonpos hpos hlower (neg_nonpos.mpr hp)
    rw [Real.mul_rpow (by positivity : 0 ≤ R / Real.pi) (abs_nonneg θ)] at hh
    exact hh.trans (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))

theorem circle_distance_rotate (R θ : ℝ) (a : ℂ) :
    ‖circleMap 0 R (θ + a.arg) - a‖ = ‖circleMap 0 R θ - (‖a‖ : ℂ)‖ := by
  have he : circleMap 0 R (θ + a.arg) - a =
      (circleMap 0 R θ - (‖a‖ : ℂ)) * Complex.exp ((a.arg : ℂ) * Complex.I) := by
    rw [sub_mul, Complex.norm_mul_exp_arg_mul_I]
    congr 1
    simp only [circleMap, zero_add, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  rw [he, norm_mul]
  simp

end ModifiedCartan
