import ModifiedCartan.PoissonExtension

noncomputable section
set_option autoImplicit false
open Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

theorem poissonExtension_nonneg {v : ℂ → ℝ} {R : ℝ}
    (hv : CircleIntegrable v 0 R) (hv0 : ∀ ζ ∈ sphere (0 : ℂ) |R|, 0 ≤ v ζ)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) : 0 ≤ poissonExtension v R w := by
  have hh := poissonExtension_mono (circleIntegrable_const (0:ℝ) 0 R) hv hv0 hw
  simpa [poissonExtension, Real.circleAverage_const] using hh

theorem poissonExtension_harnack_bounds {v : ℂ → ℝ} {R : ℝ}
    (hv : CircleIntegrable v 0 R) (hv0 : ∀ ζ ∈ sphere (0 : ℂ) |R|, 0 ≤ v ζ)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    (R - ‖w‖) / (R + ‖w‖) * poissonExtension v R 0 ≤ poissonExtension v R w ∧
    poissonExtension v R w ≤ (R + ‖w‖) / (R - ‖w‖) * poissonExtension v R 0 := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hk := Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hi := hv.continuousOn_smul hk
  rw [poissonExtension_zero hR hv, poissonExtension_eq_average hv hw]
  constructor
  · have hh := Real.circleAverage_mono
      (hv.const_smul (a := (R - ‖w‖) / (R + ‖w‖))) hi (fun ζ hζ => ?_)
    · simpa only [Real.circleAverage_smul, smul_eq_mul, Pi.mul_def, Function.comp_def] using hh
    · apply mul_le_mul_of_nonneg_right _ (hv0 ζ hζ)
      simpa only [Function.comp_def, herglotzRieszKernel_def, sub_zero] using le_re_herglotzRieszKernel (by simpa [abs_of_pos hR] using hζ) hw
  · have hh := Real.circleAverage_mono hi
      (hv.const_smul (a := (R + ‖w‖) / (R - ‖w‖))) (fun ζ hζ => ?_)
    · simpa only [Real.circleAverage_smul, smul_eq_mul, Pi.mul_def, Function.comp_def] using hh
    · apply mul_le_mul_of_nonneg_right _ (hv0 ζ hζ)
      simpa only [Function.comp_def, herglotzRieszKernel_def, sub_zero] using re_herglotzRieszKernel_le (by simpa [abs_of_pos hR] using hζ) hw

theorem poissonExtension_harnack_uniform {v : ℂ → ℝ} {R r : ℝ}
    (hv : CircleIntegrable v 0 R) (hv0 : ∀ ζ ∈ sphere (0 : ℂ) |R|, 0 ≤ v ζ)
    (hr : 0 ≤ r) (hrR : r < R) {w : ℂ} (hw : ‖w‖ ≤ r) :
    (R - r) / (R + r) * poissonExtension v R 0 ≤ poissonExtension v R w ∧
    (R - r) / (R + r) * poissonExtension v R w ≤ poissonExtension v R 0 := by
  have hR : 0 < R := hr.trans_lt hrR
  have hwr : ‖w‖ < R := hw.trans_lt hrR
  have hwb : w ∈ ball (0 : ℂ) R := by simpa using hwr
  have hc := poissonExtension_nonneg hv hv0 (mem_ball_self hR)
  have hfw := poissonExtension_nonneg hv hv0 hwb
  obtain ⟨hl, hu⟩ := poissonExtension_harnack_bounds hv hv0 hwb
  have hlower : (R - r) / (R + r) ≤ (R - ‖w‖) / (R + ‖w‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h1 := (mul_le_mul_of_nonneg_right hlower hc).trans hl
  have h2 : (R - ‖w‖) / (R + ‖w‖) * poissonExtension v R w ≤ poissonExtension v R 0 := by
    apply (mul_le_mul_of_nonneg_left hu
      (show 0 ≤ (R - ‖w‖) / (R + ‖w‖) by positivity)).trans_eq
    field_simp [ne_of_gt (sub_pos.mpr hwr), ne_of_gt (show 0 < R + ‖w‖ by positivity)]
  exact ⟨h1, (mul_le_mul_of_nonneg_right hlower hfw).trans h2⟩

theorem poissonExtension_sub {v u : ℂ → ℝ} {R : ℝ}
    (hv : CircleIntegrable v 0 R) (hu : CircleIntegrable u 0 R)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    poissonExtension (fun ζ => v ζ - u ζ) R w = poissonExtension v R w - poissonExtension u R w := by
  have hk := Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hsub : CircleIntegrable (fun ζ => v ζ - u ζ) 0 R := by simpa only [Pi.sub_def] using hv.sub hu
  rw [poissonExtension_eq_average hsub hw, poissonExtension_eq_average hv hw,
    poissonExtension_eq_average hu hw]
  simp only [mul_sub]
  simpa only [Pi.sub_def, Pi.smul_def, Pi.mul_def, Function.comp_def, smul_eq_mul] using
    Real.circleAverage_sub (hv.continuousOn_smul hk) (hu.continuousOn_smul hk)

end ModifiedCartan
