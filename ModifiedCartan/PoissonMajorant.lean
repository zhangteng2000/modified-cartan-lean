import ModifiedCartan.PoissonHarnack
import ModifiedCartan.LogPoisson
import ModifiedCartan.CircleExceptional

noncomputable section
set_option autoImplicit false
open Filter Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

theorem poissonExtension_add {v u : ℂ → ℝ} {R : ℝ}
    (hv : CircleIntegrable v 0 R) (hu : CircleIntegrable u 0 R)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    poissonExtension (fun ζ => v ζ + u ζ) R w = poissonExtension v R w + poissonExtension u R w := by
  have hk := Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hadd : CircleIntegrable (fun ζ => v ζ + u ζ) 0 R := by simpa only [Pi.add_def] using hv.add hu
  rw [poissonExtension_eq_average hadd hw, poissonExtension_eq_average hv hw,
    poissonExtension_eq_average hu hw]
  simp only [mul_add]
  simpa only [Pi.add_def, Pi.smul_def, Pi.mul_def, Function.comp_def, smul_eq_mul] using
    Real.circleAverage_add (hv.continuousOn_smul hk) (hu.continuousOn_smul hk)

theorem poissonExtension_mono_codiscrete {v u : ℂ → ℝ} {R : ℝ}
    (hv : CircleIntegrable v 0 R) (hu : CircleIntegrable u 0 R)
    (hle : ∀ᶠ ζ in codiscreteWithin (sphere (0 : ℂ) |R|), v ζ ≤ u ζ)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) : poissonExtension v R w ≤ poissonExtension u R w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hk := Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  rw [poissonExtension_eq_average hv hw, poissonExtension_eq_average hu hw]
  apply circleAverage_mono_codiscrete hR.ne' (hv.continuousOn_smul hk) (hu.continuousOn_smul hk)
  filter_upwards [hle, self_mem_codiscreteWithin (sphere (0 : ℂ) |R|)] with ζ hleζ hζ
  have hkpos : 0 ≤ (herglotzRieszKernel 0 w ζ).re := by
    apply le_trans _ (le_re_herglotzRieszKernel (by simpa [abs_of_pos hR] using hζ) hw)
    have hwn : ‖w‖ < R := by simpa using hw
    simp only [sub_zero]
    exact div_nonneg (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_left hleζ hkpos

/-- Poisson comparison with integrable logarithmic error. Boundary zeros and
the identically zero function are both permitted. -/
theorem norm_le_exp_poisson_majorant {F : ℂ → ℂ} {v e : ℂ → ℝ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R))
    (hv : CircleIntegrable v 0 R) (he : CircleIntegrable e 0 R)
    (he0 : ∀ ζ ∈ sphere (0 : ℂ) |R|, 0 ≤ e ζ)
    (hbound : ∀ᶠ ζ in codiscreteWithin (sphere (0 : ℂ) |R|),
      F ζ ≠ 0 → Real.log ‖F ζ‖ ≤ v ζ + e ζ)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    ‖F w‖ ≤ Real.exp (poissonExtension v R w +
      (R + ‖w‖) / (R - ‖w‖) * Real.circleAverage e 0 R) := by
  by_cases hwzero : F w = 0
  · rw [hwzero, norm_zero]
    exact (Real.exp_pos _).le
  have hR : 0 < R := pos_of_mem_ball hw
  have hsub : sphere (0 : ℂ) |R| ⊆ closedBall (0 : ℂ) R := by
    rw [abs_of_pos hR]
    exact sphere_subset_closedBall
  have hlog := (hF.mono hsub).meromorphicOn.circleIntegrable_log_norm
  have hnz : ∀ᶠ ζ in codiscreteWithin (sphere (0 : ℂ) |R|), F ζ ≠ 0 := by
    have hident := hF.preimage_zero_mem_codiscreteWithin hwzero (ball_subset_closedBall hw)
      ⟨⟨w, ball_subset_closedBall hw⟩, (convex_closedBall (0 : ℂ) R).isPreconnected⟩
    exact (codiscreteWithin_mono hsub) hident
  have hle : poissonExtension (fun ζ => Real.log ‖F ζ‖) R w ≤
      poissonExtension (fun ζ => v ζ + e ζ) R w :=
    poissonExtension_mono_codiscrete hlog (by simpa only [Pi.add_def] using hv.add he)
      (by filter_upwards [hbound, hnz] with ζ hb hz; exact hb hz) hw
  have hpoisson : Real.log ‖F w‖ ≤ poissonExtension (fun ζ => Real.log ‖F ζ‖) R w := by
    rw [poissonExtension_eq_average hlog hw]
    exact log_norm_le_poisson hF hw hwzero
  rw [poissonExtension_add hv he hw] at hle
  have herr := (poissonExtension_harnack_bounds he he0 hw).2
  rw [poissonExtension_zero hR he] at herr
  have hfinal : Real.log ‖F w‖ ≤ poissonExtension v R w +
      (R + ‖w‖) / (R - ‖w‖) * Real.circleAverage e 0 R := by linarith
  simpa only [Real.exp_log (norm_pos_iff.mpr hwzero)] using Real.exp_le_exp.mpr hfinal

end ModifiedCartan
