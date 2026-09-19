import ModifiedCartan.FiveExampleBounds

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real Filter Topology
namespace ModifiedCartan

theorem scaled_linear_exp_decay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x * Real.exp (-c * x)) atTop (𝓝 0) := by
  have hh := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop hc)
  have he (x : ℝ) : x * Real.exp (-c * x) = (1 / c) * ((c * x) ^ 1 * Real.exp (-(c * x))) := by
    field_simp
  simp_rw [he]
  simpa only [Function.comp_def, id_eq, mul_zero] using hh.const_mul (1 / c)

theorem fiveA_vanishes_of_negative_real_part {z : ℂ} (hz : (fiveL z).re < 0) :
    Tendsto (fun n : ℕ => fiveA ((n : ℝ) + 1) z) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hh := (scaled_linear_exp_decay (neg_pos.mpr hz)).comp hN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have he (n : ℕ) : ‖fiveA ((n : ℝ) + 1) z‖ =
      2 * (((n : ℝ) + 1) * Real.exp (-(-(fiveL z).re) * ((n : ℝ) + 1))) := by
    rw [fiveA_norm (by positivity)]
    simp only [neg_neg]
    rw [mul_comm ((n : ℝ) + 1) (fiveL z).re]
    ring
  simp_rw [he]
  simpa only [Function.comp_def, mul_zero] using hh.const_mul 2

theorem fiveA_vanishes_negative_point {t : ℝ} (htr : sharpRadius < t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => fiveA ((n : ℝ) + 1) ((-t : ℝ) : ℂ)) atTop (𝓝 0) :=
  fiveA_vanishes_of_negative_real_part ((fiveL_negative_iff (sharpRadius_pos.trans htr) ht1).mpr htr)

theorem fiveA_grows_at_zero :
    Tendsto (fun n : ℕ => ‖fiveA ((n : ℝ) + 1) 0‖) atTop atTop := by
  have hN : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono _ hN
  intro n
  rw [fiveA_norm (by positivity), fiveL_zero]
  have he : 1 ≤ Real.exp (((n : ℝ) + 1) * (1 / 2 : ℂ).re) :=
    Real.one_le_exp_iff.mpr (by norm_num; positivity)
  nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * ((n : ℝ) + 1))]

theorem fivea_sub_fiveA_grows_at_zero :
    Tendsto (fun n : ℕ => ‖fivea ((n : ℝ) + 1) 0 - fiveA ((n : ℝ) + 1) 0‖) atTop atTop := by
  have hh : Tendsto (fun n : ℕ => ‖fiveA ((n : ℝ) + 1) 0‖ - (1 / 2 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ (-(1 / 2 : ℝ)) fiveA_grows_at_zero
  apply tendsto_atTop_mono _ hh
  intro n
  have hb := norm_sub_norm_le (fiveA ((n : ℝ) + 1) 0) (fivea ((n : ℝ) + 1) 0)
  simpa only [fivea_zero, norm_div, norm_one, Complex.norm_ofNat, norm_sub_rev] using hb

theorem fivea_vanishes_of_fiveA_vanishes {z : ℂ} (hz : z ∈ disk 1)
    (hA : Tendsto (fun n : ℕ => fiveA ((n : ℝ) + 1) z) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => fivea ((n : ℝ) + 1) z) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := hA.norm.const_mul (3 / 4 : ℝ)
  simp only [norm_zero, mul_zero] at hlim
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hN0 : 0 < (n : ℝ) + 1 := by positivity
  have hb := fivea_div_fiveA_bound hN0 hz
  rw [norm_div] at hb
  have hpos : 0 < ‖fiveA ((n : ℝ) + 1) z‖ := norm_pos_iff.mpr ((fiveA_unit hN0).2 z hz)
  have hratio : 3 / (4 * ((n : ℝ) + 1)) ≤ (3 / 4 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * ((n : ℝ) + 1)) (by norm_num)).mpr
    linarith
  exact ((div_le_iff₀ hpos).mp hb).trans (mul_le_mul_of_nonneg_right hratio hpos.le)

theorem fivea_sub_fiveA_vanishes_negative_point {t : ℝ}
    (htr : sharpRadius < t) (ht1 : t < 1) :
    Tendsto (fun n : ℕ => fivea ((n : ℝ) + 1) ((-t : ℝ) : ℂ) -
      fiveA ((n : ℝ) + 1) ((-t : ℝ) : ℂ)) atTop (𝓝 0) := by
  have ht0 := sharpRadius_pos.trans htr
  have hz : ((-t : ℝ) : ℂ) ∈ disk 1 := by simpa [disk, abs_of_pos ht0] using ht1
  have hh := fiveA_vanishes_negative_point htr ht1
  simpa only [sub_zero] using (fivea_vanishes_of_fiveA_vanishes hz hh).sub hh

end ModifiedCartan
