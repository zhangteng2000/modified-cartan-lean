import ModifiedCartan.FiveExampleFunctions

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

theorem cayley_real_part (z : ℂ) :
    ((1 - z) / (1 + z)).re = (1 - ‖z‖ ^ 2) / ‖1 + z‖ ^ 2 := by
  rw [Complex.div_re, Complex.normSq_eq_norm_sq, ← add_div]
  congr 1
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem fiveL_real_part (z : ℂ) :
    (fiveL z).re = (1 - ‖z‖ ^ 2) *
      ((1 + ‖z‖ ^ 2) / ‖1 + z ^ 2‖ ^ 2 - 1 / (2 * ‖1 + z‖ ^ 2)) := by
  have he : (1 - z) / (2 * (1 + z)) = ((1 - z) / (1 + z)) / 2 := by
    rw [div_div]
    congr 1
    ring
  rw [fiveL, he, Complex.sub_re, cayley_real_part]
  have hr (w : ℂ) : (w / 2).re = w.re / 2 := by simp [Complex.div_re]
  rw [hr, cayley_real_part, norm_pow]
  ring

set_option maxHeartbeats 800000 in
theorem fiveL_re_pos_right {z : ℂ} (hz : z ∈ disk 1) (hx : 0 ≤ z.re) :
    0 < (fiveL z).re := by
  have hzn : ‖z‖ < 1 := by simpa [disk] using hz
  have h1 : 1 + z ≠ 0 := by simpa using disk_one_add_pow_ne_zero hz (by norm_num : (1 : ℕ) ≠ 0)
  have h2 := disk_one_add_pow_ne_zero hz (by norm_num : (2 : ℕ) ≠ 0)
  have hd1 : 0 < ‖1 + z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr h1)
  have hd2 : 0 < ‖1 + z ^ 2‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr h2)
  have hid : 2 * (1 + ‖z‖ ^ 2) * ‖1 + z‖ ^ 2 - ‖1 + z ^ 2‖ ^ 2 =
      (1 + ‖z‖ ^ 2) ^ 2 + 4 * z.re * (1 + ‖z‖ ^ 2) + 4 * z.im ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply]
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have hnum : ‖1 + z ^ 2‖ ^ 2 < 2 * (1 + ‖z‖ ^ 2) * ‖1 + z‖ ^ 2 := by
    have hp : 0 < (1 + ‖z‖ ^ 2) ^ 2 + 4 * z.re * (1 + ‖z‖ ^ 2) + 4 * z.im ^ 2 := by
      positivity
    linarith
  rw [fiveL_real_part]
  apply mul_pos
  · nlinarith [norm_nonneg z]
  · apply sub_pos.mpr
    apply (div_lt_div_iff₀ (mul_pos (by norm_num) hd1) hd2).mpr
    nlinarith only [hnum]

theorem five_majorant_positive_gap {z : ℂ} (hz : z ∈ disk 1) :
    -(fivePhi z ^ 2).re < (fiveL z).re := by
  have hh := congrArg Complex.re (five_majorant_identity hz)
  have he : ((1 + z) / (2 * (1 - z))).re =
      ((1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2) / 2 := by
    have hrewrite : (1 + z) / (2 * (1 - z)) = ((1 - -z) / (1 + -z)) / 2 := by
      rw [div_div]
      simp only [sub_neg_eq_add, ← sub_eq_add_neg]
      congr 1
      ring
    rw [hrewrite]
    have hr (w : ℂ) : (w / 2).re = w.re / 2 := by simp [Complex.div_re]
    rw [hr, cayley_real_part, norm_neg]
    simp only [← sub_eq_add_neg]
  rw [he, Complex.add_re] at hh
  have hzn : ‖z‖ < 1 := by simpa [disk] using hz
  have hd : 1 - z ≠ 0 := by
    have hpos := disk_one_sub_pow_re_pos hz (by norm_num : (1 : ℕ) ≠ 0)
    simp only [pow_one] at hpos
    intro he
    simp [he] at hpos
  have hp : 0 < ((1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2) / 2 := by
    apply div_pos _ (by norm_num)
    exact div_pos (by nlinarith [norm_nonneg z]) (sq_pos_of_pos (norm_pos_iff.mpr hd))
  linarith

end ModifiedCartan
