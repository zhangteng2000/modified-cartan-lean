import ModifiedCartan.FiveExampleFunctions

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

set_option maxHeartbeats 800000 in
theorem fivePhi_re_factor {z : ℂ} (hz : z ∈ disk 1) :
    ∃ c : ℝ, 0 < c ∧ (fivePhi z).re = c * z.re := by
  let d := Complex.sqrt (1 - z ^ 4)
  have hpos := disk_one_sub_pow_re_pos hz (by norm_num : (4 : ℕ) ≠ 0)
  have hdre : 0 < d.re := by
    change 0 < ((1 - z ^ 4) ^ (2⁻¹ : ℂ)).re
    rw [Complex.cpow_inv_two_re]
    exact Real.sqrt_pos.mpr (by positivity)
  have hdn : 0 < Complex.normSq d := Complex.normSq_pos.mpr (by
    intro he
    simp [he] at hdre)
  have hdre2 : d.re ^ 2 = (‖1 - z ^ 4‖ + (1 - z ^ 4).re) / 2 := by
    change (((1 - z ^ 4) ^ (2⁻¹ : ℂ)).re) ^ 2 = _
    rw [Complex.cpow_inv_two_re, Real.sq_sqrt (by positivity)]
  have hre : (1 - z ^ 4).re = 1 - (z.re ^ 4 - 6 * z.re ^ 2 * z.im ^ 2 + z.im ^ 4) := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  have him : (1 - z ^ 4).im = -4 * z.re * z.im * (z.re ^ 2 - z.im ^ 2) := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  have hdi : 2 * d.re * d.im = -4 * z.re * z.im * (z.re ^ 2 - z.im ^ 2) := by
    have hh := congrArg Complex.im (complex_sqrt_sq (1 - z ^ 4))
    change (d ^ 2).im = (1 - z ^ 4).im at hh
    rw [him] at hh
    simp only [pow_two, Complex.mul_im] at hh
    nlinarith [hh]
  have hzn : ‖z‖ < 1 := by simpa [disk] using hz
  have hx : |z.re| < 1 := (Complex.abs_re_le_norm z).trans_lt hzn
  have hx2 : z.re ^ 2 < 1 := by nlinarith [sq_abs z.re, abs_nonneg z.re]
  have hx4 : z.re ^ 4 < 1 := by nlinarith [sq_nonneg z.re]
  let B := d.re ^ 2 - 2 * z.im ^ 2 * (z.re ^ 2 - z.im ^ 2)
  have hB : 0 < B := by
    rw [hre] at hdre2
    dsimp [B]
    nlinarith [norm_nonneg (1 - z ^ 4), sq_nonneg (z.re * z.im), sq_nonneg (z.im ^ 2)]
  have hid : (fivePhi z).re * (Complex.normSq d * d.re) = 2 * B * z.re := by
    change (2 * z / d).re * (Complex.normSq d * d.re) = _
    rw [Complex.div_re]
    norm_num [Complex.mul_re, Complex.mul_im]
    field_simp [hdn.ne']
    dsimp [B]
    nlinarith [congrArg (fun x : ℝ => x * z.im) hdi]
  refine ⟨2 * B / (Complex.normSq d * d.re), div_pos (by positivity) (mul_pos hdn hdre), ?_⟩
  calc
    _ = (2 * B * z.re) / (Complex.normSq d * d.re) := (eq_div_iff (mul_pos hdn hdre).ne').mpr hid
    _ = _ := by ring

theorem fivePhi_re_nonpos_iff {z : ℂ} (hz : z ∈ disk 1) :
    (fivePhi z).re ≤ 0 ↔ z.re ≤ 0 := by
  obtain ⟨c, hc, he⟩ := fivePhi_re_factor hz
  rw [he]
  constructor <;> intro h <;> nlinarith

theorem fivePhi_re_nonneg_iff {z : ℂ} (hz : z ∈ disk 1) :
    0 ≤ (fivePhi z).re ↔ 0 ≤ z.re := by
  obtain ⟨c, hc, he⟩ := fivePhi_re_factor hz
  rw [he, mul_nonneg_iff_of_pos_left hc]

end ModifiedCartan
