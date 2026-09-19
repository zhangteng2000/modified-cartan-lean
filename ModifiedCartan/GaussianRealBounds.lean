import ModifiedCartan.GaussianPrimitive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory Metric Set Filter Topology
namespace ModifiedCartan

theorem gaussian_normalization {n : ℝ} (hn : 0 < n) :
    Real.sqrt (n / Real.pi) * Real.sqrt (Real.pi / n) = 1 := by
  rw [← Real.sqrt_mul (div_nonneg hn.le Real.pi_pos.le)]
  have he : n / Real.pi * (Real.pi / n) = 1 := by field_simp
  rw [he, Real.sqrt_one]

theorem gaussianTransition_real (n x : ℝ) :
    gaussianTransition n (x : ℂ) =
      ((1 / 2 + Real.sqrt (n / Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-n * t ^ 2) : ℝ) : ℂ) := by
  have hker (t : ℝ) : gaussianKernel n (t : ℂ) = (Real.exp (-n * t ^ 2) : ℂ) := by
    simp [gaussianKernel]
  rw [gaussianTransition, gaussianPrimitive_real]
  simp_rw [hker]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  rfl

theorem integral_gaussian_Iic (n : ℝ) :
    ∫ t in Iic (0 : ℝ), Real.exp (-n * t ^ 2) = Real.sqrt (Real.pi / n) / 2 := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), Real.exp (-n * (-t) ^ 2) := by
      simpa only [neg_zero] using
        (integral_comp_neg_Ioi (0 : ℝ) (fun t => Real.exp (-n * t ^ 2))).symm
    _ = _ := by simpa only [neg_sq] using integral_gaussian_Ioi n

theorem gaussianTransition_real_tendsto_zero {n : ℝ} (hn : 0 < n) :
    Tendsto (fun x : ℝ => gaussianTransition n (x : ℂ)) atBot (𝓝 0) := by
  have hi := intervalIntegral_tendsto_integral_Iic (0 : ℝ)
    (integrable_exp_neg_mul_sq hn).integrableOn (tendsto_id : Tendsto (id : ℝ → ℝ) atBot atBot)
  rw [integral_gaussian_Iic] at hi
  have hl : Tendsto (fun x : ℝ => (1 / 2 : ℝ) -
      Real.sqrt (n / Real.pi) * ∫ t in x..0, Real.exp (-n * t ^ 2)) atBot
      (𝓝 ((1 / 2 : ℝ) - Real.sqrt (n / Real.pi) * (Real.sqrt (Real.pi / n) / 2))) :=
    tendsto_const_nhds.sub (hi.const_mul (Real.sqrt (n / Real.pi)))
  have hv : (1 / 2 : ℝ) - Real.sqrt (n / Real.pi) * (Real.sqrt (Real.pi / n) / 2) = 0 := by
    rw [← mul_div_assoc, gaussian_normalization hn]
    ring
  rw [hv] at hl
  have he (x : ℝ) : gaussianTransition n (x : ℂ) =
      (((1 / 2 : ℝ) - Real.sqrt (n / Real.pi) * ∫ t in x..0, Real.exp (-n * t ^ 2)) : ℂ) := by
    rw [gaussianTransition_real, intervalIntegral.integral_symm 0 x]
    push_cast
    ring
  simp_rw [he]
  exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hl

theorem gaussian_integral_zero_bound {n b : ℝ} (hn : 0 < n) (hb : 0 ≤ b) :
    (∫ t in (0 : ℝ)..b, Real.exp (-n * t ^ 2)) ≤ Real.sqrt (Real.pi / n) / 2 := by
  rw [intervalIntegral.integral_of_le hb, ← integral_gaussian_Ioi n]
  exact setIntegral_mono_set (integrable_exp_neg_mul_sq hn).integrableOn
    (Eventually.of_forall (fun t => (Real.exp_pos _).le))
    (show Ioc (0 : ℝ) b ⊆ Ioi 0 from fun t ht => ht.1).eventuallyLE

/-- The Gaussian left-tail estimate with the manuscript's exact one-half factor. -/
theorem gaussian_interval_left_bound {n a x : ℝ} (hn : 0 < n) (hax : a ≤ x) (hx : x ≤ 0) :
    (∫ t in a..x, Real.exp (-n * t ^ 2)) ≤
      Real.exp (-n * x ^ 2) * (Real.sqrt (Real.pi / n) / 2) := by
  have hsub : (∫ t in a..x, Real.exp (-n * t ^ 2)) =
      ∫ t in (0 : ℝ)..(x - a), Real.exp (-n * (x - t) ^ 2) := by
    simpa only [sub_zero, sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left (a := 0) (b := x - a)
        (fun t : ℝ => Real.exp (-n * t ^ 2)) x).symm
  rw [hsub]
  calc
    _ ≤ ∫ t in (0 : ℝ)..(x - a), Real.exp (-n * x ^ 2) * Real.exp (-n * t ^ 2) := by
      apply intervalIntegral.integral_mono_on (sub_nonneg.mpr hax)
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)
      intro t ht
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm : x * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx ht.1
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hn.le hm]
    _ = Real.exp (-n * x ^ 2) * ∫ t in (0 : ℝ)..(x - a), Real.exp (-n * t ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_integral_zero_bound hn (sub_nonneg.mpr hax))
      (Real.exp_pos _).le

end ModifiedCartan
