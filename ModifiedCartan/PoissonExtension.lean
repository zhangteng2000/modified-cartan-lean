import ModifiedCartan.Harmonic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

noncomputable section
set_option autoImplicit false
open Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

/-- The genuine Poisson extension, defined through the analytic Herglotz integral. -/
def poissonExtension (v : ℂ → ℝ) (R : ℝ) (w : ℂ) : ℝ :=
  (Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (v ζ : ℂ)) 0 R).re

theorem poissonExtension_eq_average {v : ℂ → ℝ} {R : ℝ}
    (hv : CircleIntegrable v 0 R) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    poissonExtension v R w = Real.circleAverage
      (fun ζ => (herglotzRieszKernel 0 w ζ).re * v ζ) 0 R := by
  exact re_circleAverage_herglotzRieszKernel_smul hv hw

theorem poissonExtension_harmonic {v : ℂ → ℝ} {R : ℝ}
    (hv : CircleIntegrable v 0 R) : HarmonicOnNhd (poissonExtension v R) (ball (0 : ℂ) R) := by
  have hcomplex : CircleIntegrable (fun ζ => (v ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hv ⊢
    exact Complex.ofRealCLM.integrable_comp hv
  intro w hw
  exact (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hcomplex w hw).harmonicAt_re

theorem poissonExtension_zero {v : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv : CircleIntegrable v 0 R) : poissonExtension v R 0 = Real.circleAverage v 0 R := by
  rw [poissonExtension_eq_average hv (mem_ball_self hR)]
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  have hζ0 : ζ ≠ 0 := by
    intro he
    subst ζ
    have he : (0 : ℝ) = R := by simpa [abs_of_pos hR] using hζ
    linarith
  simp [herglotzRieszKernel_def, hζ0]

theorem poissonExtension_mono {v u : ℂ → ℝ} {R : ℝ}
    (hv : CircleIntegrable v 0 R) (hu : CircleIntegrable u 0 R)
    (hle : ∀ ζ ∈ sphere (0 : ℂ) |R|, v ζ ≤ u ζ)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) : poissonExtension v R w ≤ poissonExtension u R w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hk := Complex.continuous_re.comp_continuousOn
    (continuousOn_herglotzRieszKernel_sphere hw)
  rw [poissonExtension_eq_average hv hw, poissonExtension_eq_average hu hw]
  apply Real.circleAverage_mono (hv.continuousOn_smul hk) (hu.continuousOn_smul hk)
  intro ζ hζ
  have hkpos : 0 ≤ (herglotzRieszKernel 0 w ζ).re := by
    apply le_trans _ (le_re_herglotzRieszKernel (by simpa [abs_of_pos hR] using hζ) hw)
    have hwn : ‖w‖ < R := by simpa using hw
    simp only [sub_zero]
    exact div_nonneg (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_left (hle ζ hζ) hkpos

theorem poissonExtension_eq_harmonic {u : ℂ → ℝ} {R : ℝ}
    (hu : HarmonicContOnCl u (ball (0 : ℂ) R)) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    poissonExtension u R w = u w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hi : CircleIntegrable u 0 R := by
    apply ContinuousOn.circleIntegrable'
    simpa [abs_of_pos hR] using hu.continuousOn_ball.mono sphere_subset_closedBall
  rw [poissonExtension_eq_average hi hw]
  exact hu.circleAverage_re_herglotzRieszKernel_smul hw

theorem harmonic_le_poissonExtension {u v : ℂ → ℝ} {R : ℝ}
    (hu : HarmonicContOnCl u (ball (0 : ℂ) R)) (hv : CircleIntegrable v 0 R)
    (hbound : ∀ ζ ∈ sphere (0 : ℂ) |R|, u ζ ≤ v ζ)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) : u w ≤ poissonExtension v R w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hi : CircleIntegrable u 0 R := by
    apply ContinuousOn.circleIntegrable'
    simpa [abs_of_pos hR] using hu.continuousOn_ball.mono sphere_subset_closedBall
  rw [← poissonExtension_eq_harmonic hu hw]
  exact poissonExtension_mono hi hv hbound hw

end ModifiedCartan
