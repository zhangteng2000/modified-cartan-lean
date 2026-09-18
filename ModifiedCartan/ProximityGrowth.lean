import ModifiedCartan.LogPoisson

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

theorem log_norm_le_proximity {F : ℂ → ℂ} {R : ℝ} {w : ℂ}
    (hF : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R))
    (hw : w ∈ ball (0 : ℂ) R) (hwne : F w ≠ 0) :
    Real.log ‖F w‖ ≤ (R + ‖w‖) / (R - ‖w‖) * proximityMean F R := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hwR : ‖w‖ < R := by simpa using hw
  let q := (R + ‖w‖) / (R - ‖w‖)
  let P := Complex.re ∘ herglotzRieszKernel 0 w
  have hFs : MeromorphicOn F (sphere (0 : ℂ) |R|) := by
    simpa [abs_of_pos hR] using (hF.mono sphere_subset_closedBall).meromorphicOn
  have hlogi := hFs.circleIntegrable_log_norm
  have hposi := hFs.circleIntegrable_posLog_norm
  have hPc : ContinuousOn P (sphere (0 : ℂ) |R|) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hmono := circleAverage_mono (hlogi.continuousOn_smul hPc)
    (hposi.const_smul (a := q)) (fun z hz => ?_)
  · have hp := (log_norm_le_poisson hF hw hwne).trans hmono
    rw [circleAverage_smul] at hp
    simpa only [proximityMean, ValueDistribution.proximity_top, smul_eq_mul] using hp
  · have hz' : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hz
    have hlo : (R - ‖w‖) / (R + ‖w‖) ≤ P z := by
      simpa [P, Function.comp_apply, herglotzRieszKernel, sub_zero] using
        le_re_herglotzRieszKernel hz' hw
    have hhi : P z ≤ q := by
      simpa [q, P, Function.comp_apply, herglotzRieszKernel, sub_zero] using
        re_herglotzRieszKernel_le hz' hw
    have hP : 0 ≤ P z := (div_nonneg (by linarith) (by positivity)).trans hlo
    change P z * Real.log ‖F z‖ ≤ q * Real.posLog ‖F z‖
    exact (mul_le_mul_of_nonneg_left (by simp [Real.posLog_apply]) hP).trans
      (mul_le_mul_of_nonneg_right hhi Real.posLog_nonneg)

theorem norm_le_exp_proximity {F : ℂ → ℂ} {R : ℝ} {w : ℂ}
    (hF : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R)) (hw : w ∈ ball (0 : ℂ) R) :
    ‖F w‖ ≤ Real.exp ((R + ‖w‖) / (R - ‖w‖) * proximityMean F R) := by
  by_cases hzero : F w = 0
  · simp only [hzero, norm_zero]
    exact (Real.exp_pos _).le
  · have he := Real.exp_le_exp.mpr (log_norm_le_proximity hF hw hzero)
    rwa [Real.exp_log (norm_pos_iff.mpr hzero)] at he

theorem norm_le_exp_proximity_on_closedBall {F : ℂ → ℂ} {S R : ℝ}
    (hS : 0 ≤ S) (hSR : S < R)
    (hF : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R)) {w : ℂ} (hw : ‖w‖ ≤ S) :
    ‖F w‖ ≤ Real.exp ((R + S) / (R - S) * proximityMean F R) := by
  have hR : 0 < R := hS.trans_lt hSR
  apply (norm_le_exp_proximity hF (by simpa using hw.trans_lt hSR)).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ (ValueDistribution.proximity_nonneg R)
  apply (div_le_div_iff₀ (by linarith : 0 < R - ‖w‖) (by linarith : 0 < R - S)).mpr
  nlinarith

/-- The first bound in the proof of `lem:logderivative`, with an explicit constant 4. -/
theorem norm_le_exp_proximity_midpoint {F : ℂ → ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR1 : R ≤ 1)
    (hF : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R)) {w : ℂ} (hw : ‖w‖ ≤ (r + R) / 2) :
    ‖F w‖ ≤ Real.exp (1 + 4 * proximityMean F R / (R - r)) := by
  have hmid : 0 ≤ (r + R) / 2 := by linarith
  have hmidR : (r + R) / 2 < R := by linarith
  apply (norm_le_exp_proximity_on_closedBall hmid hmidR hF hw).trans
  apply Real.exp_le_exp.mpr
  have hq : (R + (r + R) / 2) / (R - (r + R) / 2) ≤ 4 / (R - r) := by
    apply (div_le_div_iff₀ (by linarith : 0 < R - (r + R) / 2) (by linarith : 0 < R - r)).mpr
    nlinarith
  have hm : 0 ≤ proximityMean F R := ValueDistribution.proximity_nonneg R
  have hmul := mul_le_mul_of_nonneg_right hq hm
  have he : 4 / (R - r) * proximityMean F R = 4 * proximityMean F R / (R - r) := by ring
  rw [he] at hmul
  linarith only [hmul]

end ModifiedCartan
