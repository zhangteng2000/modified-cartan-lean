import ModifiedCartan.GaussianRealBounds

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory Metric Set Filter Topology
open scoped Interval
namespace ModifiedCartan

theorem gaussian_horizontal_norm_bound {n a x y : ℝ} (hn : 0 < n) (hax : a ≤ x) (hx : x ≤ 0) :
    ‖∫ t in a..x, gaussianKernel n ((t : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp (-n * (x ^ 2 - y ^ 2)) * (Real.sqrt (Real.pi / n) / 2) := by
  have he (t : ℝ) : ‖gaussianKernel n ((t : ℂ) + (y : ℂ) * I)‖ =
      Real.exp (n * y ^ 2) * Real.exp (-n * t ^ 2) := by
    rw [gaussianKernel_norm]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ∫ t in a..x, ‖gaussianKernel n ((t : ℂ) + (y : ℂ) * I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hax
    _ = Real.exp (n * y ^ 2) * ∫ t in a..x, Real.exp (-n * t ^ 2) := by
      simp_rw [he]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.exp (n * y ^ 2) *
        (Real.exp (-n * x ^ 2) * (Real.sqrt (Real.pi / n) / 2)) :=
      mul_le_mul_of_nonneg_left (gaussian_interval_left_bound hn hax hx) (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem gaussian_vertical_norm_bound {n a y : ℝ} (hn : 0 < n) :
    ‖I * ∫ t in (0 : ℝ)..y, gaussianKernel n ((a : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp (-n * (a ^ 2 - y ^ 2)) * |y| := by
  rw [norm_mul, Complex.norm_I, one_mul]
  have hbound : ∀ t ∈ Ι (0 : ℝ) y,
      ‖gaussianKernel n ((a : ℂ) + (t : ℂ) * I)‖ ≤ Real.exp (-n * (a ^ 2 - y ^ 2)) := by
    intro t ht
    have ht2 : t ^ 2 ≤ y ^ 2 := by
      rcases mem_uIoc.mp ht with hh | hh
      · exact (sq_le_sq₀ hh.1.le (hh.1.le.trans hh.2)).mpr hh.2
      · have hty : -t ≤ -y := neg_le_neg hh.1.le
        have hsq := (sq_le_sq₀ (neg_nonneg.mpr hh.2)
          (neg_nonneg.mpr (hh.1.le.trans hh.2))).mpr hty
        simpa only [neg_sq] using hsq
    rw [gaussianKernel_norm]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left ht2 hn.le]
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const hbound

theorem gaussianPrimitive_horizontal_shift (n a : ℝ) (w : ℂ) :
    gaussianPrimitive n w - gaussianPrimitive n (a : ℂ) =
      (∫ t in a..w.re, gaussianKernel n ((t : ℂ) + (w.im : ℂ) * I)) +
        I * ∫ t in (0 : ℝ)..w.im, gaussianKernel n ((a : ℂ) + (t : ℂ) * I) := by
  have hh := gaussianPrimitive_sub n (a : ℂ) w
  rw [Complex.wedgeIntegral] at hh
  simp only [ofReal_re, ofReal_im, smul_eq_mul] at hh
  rw [intervalIntegral.integral_symm a w.re,
    intervalIntegral.integral_symm 0 w.im] at hh
  linear_combination -hh

/-- Finite-contour estimate before letting its left edge tend to minus infinity. -/
theorem gaussianTransition_left_finite_bound {n a : ℝ} (hn : 0 < n) {w : ℂ}
    (hax : a ≤ w.re) (hx : w.re ≤ 0) :
    ‖gaussianTransition n w‖ ≤ ‖gaussianTransition n (a : ℂ)‖ +
      (1 / 2) * Real.exp (-n * (w.re ^ 2 - w.im ^ 2)) +
      Real.sqrt (n / Real.pi) * Real.exp (-n * (a ^ 2 - w.im ^ 2)) * |w.im| := by
  let c := Real.sqrt (n / Real.pi)
  let H := ∫ t in a..w.re, gaussianKernel n ((t : ℂ) + (w.im : ℂ) * I)
  let V := I * ∫ t in (0 : ℝ)..w.im, gaussianKernel n ((a : ℂ) + (t : ℂ) * I)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hid : gaussianTransition n w = gaussianTransition n (a : ℂ) + (c : ℂ) * H + (c : ℂ) * V := by
    have hh := gaussianPrimitive_horizontal_shift n a w
    dsimp [gaussianTransition, H, V]
    linear_combination (c : ℂ) * hh
  have hnH := gaussian_horizontal_norm_bound (y := w.im) hn hax hx
  have hnV := gaussian_vertical_norm_bound (a := a) (y := w.im) hn
  have hmul : c * (Real.exp (-n * (w.re ^ 2 - w.im ^ 2)) * (Real.sqrt (Real.pi / n) / 2)) =
      (1 / 2) * Real.exp (-n * (w.re ^ 2 - w.im ^ 2)) := by
    have hh := gaussian_normalization hn
    change c * Real.sqrt (Real.pi / n) = 1 at hh
    nlinarith [congrArg (fun x : ℝ => x * Real.exp (-n * (w.re ^ 2 - w.im ^ 2))) hh]
  calc
    _ ≤ ‖gaussianTransition n (a : ℂ)‖ + c * ‖H‖ + c * ‖V‖ := by
      rw [hid]
      have h := (norm_add_le (gaussianTransition n (a : ℂ) + (c : ℂ) * H) ((c : ℂ) * V)).trans
        (add_le_add (norm_add_le (gaussianTransition n (a : ℂ)) ((c : ℂ) * H)) le_rfl)
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] using h
    _ ≤ ‖gaussianTransition n (a : ℂ)‖ +
        c * (Real.exp (-n * (w.re ^ 2 - w.im ^ 2)) * (Real.sqrt (Real.pi / n) / 2)) +
        c * (Real.exp (-n * (a ^ 2 - w.im ^ 2)) * |w.im|) := by
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnH hc))
        (mul_le_mul_of_nonneg_left hnV hc)
    _ = _ := by rw [hmul]; ring

theorem gaussianTransition_left_bound {n : ℝ} (hn : 0 < n) {w : ℂ} (hw : w.re ≤ 0) :
    ‖gaussianTransition n w‖ ≤ (1 / 2) * Real.exp (-n * (w.re ^ 2 - w.im ^ 2)) := by
  have hG := ((gaussianTransition_real_tendsto_zero hn).comp tendsto_neg_atTop_atBot).norm
  have he : Tendsto (fun T : ℝ => Real.exp (-n * T ^ 2)) atTop (𝓝 0) :=
    (exp_neg_mul_sq_isLittleO_exp_neg hn).tendsto_zero_of_tendsto
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  have hV : Tendsto (fun T : ℝ =>
      Real.sqrt (n / Real.pi) * Real.exp (-n * ((-T) ^ 2 - w.im ^ 2)) * |w.im|) atTop (𝓝 0) := by
    have heq (T : ℝ) : Real.exp (-n * ((-T) ^ 2 - w.im ^ 2)) =
        Real.exp (n * w.im ^ 2) * Real.exp (-n * T ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [heq]
    simpa only [mul_zero, zero_mul] using ((he.const_mul (Real.exp (n * w.im ^ 2))).const_mul
      (Real.sqrt (n / Real.pi))).mul_const |w.im|
  have hl := (hG.add_const ((1 / 2) * Real.exp (-n * (w.re ^ 2 - w.im ^ 2)))).add hV
  simp only [norm_zero, zero_add, add_zero] at hl
  apply ge_of_tendsto hl
  filter_upwards [eventually_ge_atTop (-w.re)] with T hT
  exact gaussianTransition_left_finite_bound hn (by linarith) hw

theorem gaussianTransition_right_bound {n : ℝ} (hn : 0 < n) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖gaussianTransition n w‖ ≤ 1 + (1 / 2) * Real.exp (-n * (w.re ^ 2 - w.im ^ 2)) := by
  have he : gaussianTransition n w = 1 - gaussianTransition n (-w) :=
    eq_sub_iff_add_eq.mpr (gaussianTransition_symmetry n w)
  have hh := gaussianTransition_left_bound hn
    (show (-w).re ≤ 0 by simpa using hw)
  simp only [neg_re, neg_im, neg_sq] at hh
  calc
    _ = ‖1 - gaussianTransition n (-w)‖ := congrArg norm he
    _ ≤ 1 + ‖gaussianTransition n (-w)‖ := by simpa using norm_sub_le (1 : ℂ) (gaussianTransition n (-w))
    _ ≤ _ := add_le_add le_rfl hh

end ModifiedCartan
