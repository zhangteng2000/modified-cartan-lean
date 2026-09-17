import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Tactic

/-! Harnack estimates derived from mathlib's Poisson formula. -/
noncomputable section
open Complex InnerProductSpace Metric Real
namespace ModifiedCartan

/-- Boundary nonnegativity suffices for the two sharp, centered Harnack bounds. -/
theorem harmonic_harnack_bounds {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R)
    (hboundary : ∀ z ∈ sphere c R, 0 ≤ f z) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w ∧
    f w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hcont : ContinuousOn f (sphere c |R|) := by
    simpa [abs_of_pos hR] using hf.continuousOn_ball.mono sphere_subset_closedBall
  have hi : CircleIntegrable f c R := hcont.circleIntegrable'
  have hk : CircleIntegrable ((Complex.re ∘ herglotzRieszKernel c w) • f) c R :=
    ((Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hw)).smul hcont).circleIntegrable'
  have hmean : circleAverage f c R = f c :=
    (show HarmonicContOnCl f (ball c |R|) by simpa [abs_of_pos hR] using hf).circleAverage_eq
  have hpoisson := hf.circleAverage_re_herglotzRieszKernel_smul hw
  constructor
  · have h := circleAverage_mono
      (hi.const_smul (a := (R - ‖w - c‖) / (R + ‖w - c‖))) hk (fun z hz => ?_)
    · rw [hpoisson, circleAverage_smul, hmean] at h
      exact h
    · have hz' : z ∈ sphere c R := by simpa [abs_of_pos hR] using hz
      exact mul_le_mul_of_nonneg_right (le_re_herglotzRieszKernel hz' hw) (hboundary z hz')
  · have h := circleAverage_mono hk
      (hi.const_smul (a := (R + ‖w - c‖) / (R - ‖w - c‖))) (fun z hz => ?_)
    · rw [hpoisson, circleAverage_smul, hmean] at h
      exact h
    · have hz' : z ∈ sphere c R := by simpa [abs_of_pos hR] using hz
      exact mul_le_mul_of_nonneg_right (re_herglotzRieszKernel_le hz' hw) (hboundary z hz')

/-- A harmonic function with nonnegative boundary values is nonnegative in the disk. -/
theorem harmonic_nonneg_of_boundary {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : HarmonicContOnCl f (ball c R))
    (hboundary : ∀ z ∈ sphere c R, 0 ≤ f z) {w : ℂ} (hw : w ∈ ball c R) :
    0 ≤ f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hmean : circleAverage f c R = f c :=
    (show HarmonicContOnCl f (ball c |R|) by simpa [abs_of_pos hR] using hf).circleAverage_eq
  have hc : 0 ≤ f c := by
    rw [← hmean]
    exact circleAverage_nonneg_of_nonneg (by simpa [abs_of_pos hR] using hboundary)
  have hdist : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  exact (mul_nonneg (div_nonneg (by linarith) (by positivity)) hc).trans
    (harmonic_harnack_bounds hf hw hboundary).1

/-- Harnack comparison using any common upper bound r on the distance from the center. -/
theorem harmonic_harnack_uniform {f : ℂ → ℝ} {c w : ℂ} {R r : ℝ}
    (hf : HarmonicContOnCl f (ball c R))
    (hboundary : ∀ z ∈ sphere c R, 0 ≤ f z)
    (hr : 0 ≤ r) (hrR : r < R) (hw : ‖w - c‖ ≤ r) :
    (R - r) / (R + r) * f c ≤ f w ∧
    (R - r) / (R + r) * f w ≤ f c := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hwr : ‖w - c‖ < R := hw.trans_lt hrR
  have hwb : w ∈ ball c R := mem_ball_iff_norm.mpr hwr
  have hcenter : c ∈ ball c R := mem_ball_self hR
  have hc := harmonic_nonneg_of_boundary hf hboundary hcenter
  have hfw := harmonic_nonneg_of_boundary hf hboundary hwb
  obtain ⟨hl, hu⟩ := harmonic_harnack_bounds hf hwb hboundary
  have hlower : (R - r) / (R + r) ≤ (R - ‖w - c‖) / (R + ‖w - c‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h1 := (mul_le_mul_of_nonneg_right hlower hc).trans hl
  have h2 : (R - ‖w - c‖) / (R + ‖w - c‖) * f w ≤ f c := by
    apply (mul_le_mul_of_nonneg_left hu
      (show 0 ≤ (R - ‖w - c‖) / (R + ‖w - c‖) by positivity)).trans_eq
    field_simp [ne_of_gt (sub_pos.mpr hwr), ne_of_gt (show 0 < R + ‖w - c‖ by positivity)]
  exact ⟨h1, (mul_le_mul_of_nonneg_right hlower hfw).trans h2⟩

end ModifiedCartan
