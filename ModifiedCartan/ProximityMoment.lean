import ModifiedCartan.AnalyticStatements
import Mathlib.MeasureTheory.Integral.CircleAverage

noncomputable section
set_option autoImplicit false
open Real
namespace ModifiedCartan

theorem posLog_le_log_power {x p : ℝ} (hx : 0 ≤ x) (_hp : 0 < p) :
    p * Real.posLog x ≤ Real.log (1 + x ^ p) := by
  by_cases hx1 : x ≤ 1
  · have hl : Real.log x ≤ 0 := Real.log_nonpos hx hx1
    rw [Real.posLog_apply, max_eq_left hl, mul_zero]
    exact Real.log_nonneg (by linarith [Real.rpow_nonneg hx p])
  · have hxpos : 0 < x := by linarith
    have hl := Real.log_le_log (Real.rpow_pos_of_pos hxpos p)
      (show x ^ p ≤ 1 + x ^ p by linarith)
    rw [Real.log_rpow hxpos] at hl
    simpa only [Real.posLog_apply, max_eq_right (Real.log_nonneg (by linarith : 1 ≤ x))] using hl

theorem log_tangent_bound {x A : ℝ} (hx : 0 < x) (hA : 0 < A) :
    Real.log x ≤ Real.log A - 1 + A⁻¹ * x := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hA)
  rw [Real.log_div hx.ne' hA.ne', div_eq_mul_inv] at hh
  nlinarith only [hh]

/-- Jensen's logarithmic moment estimate, proved via the tangent inequality. -/
theorem proximity_le_log_moment {f : ℂ → ℂ} {R p : ℝ} (hp : 0 < p)
    (hlog : CircleIntegrable (fun z => Real.posLog ‖f z‖) 0 R)
    (hmoment : CircleIntegrable (fun z => ‖f z‖ ^ p) 0 R) :
    proximityMean f R ≤ (1 / p) * Real.log
      (1 + Real.circleAverage (fun z => ‖f z‖ ^ p) 0 R) := by
  let v : ℂ → ℝ := fun z => ‖f z‖ ^ p
  let A := 1 + Real.circleAverage v 0 R
  have havg : 0 ≤ Real.circleAverage v 0 R :=
    Real.circleAverage_nonneg_of_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hA : 0 < A := by dsimp [A]; linarith
  let u : ℂ → ℝ := (fun _ => Real.log A - 1) + A⁻¹ • ((fun _ => 1) + v)
  have hui : CircleIntegrable u 0 R :=
    (circleIntegrable_const _ _ _).add (((circleIntegrable_const _ _ _).add hmoment).const_smul)
  have hle : ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
      (p • (fun z => Real.posLog ‖f z‖)) z ≤ u z := by
    intro z _
    exact (posLog_le_log_power (norm_nonneg _) hp).trans
      (log_tangent_bound (by positivity : 0 < 1 + ‖f z‖ ^ p) hA)
  have hm := Real.circleAverage_mono (hlog.const_smul (a := p)) hui hle
  have hu : Real.circleAverage u 0 R = Real.log A := by
    dsimp [u]
    rw [Real.circleAverage_add (circleIntegrable_const _ _ _)
      (((circleIntegrable_const _ _ _).add hmoment).const_smul), Real.circleAverage_smul,
      Real.circleAverage_add (circleIntegrable_const _ _ _) hmoment]
    simp only [Real.circleAverage_const, smul_eq_mul]
    change Real.log A - 1 + A⁻¹ * A = Real.log A
    rw [inv_mul_cancel₀ hA.ne']
    ring
  rw [hu, Real.circleAverage_smul] at hm
  change p * proximityMean f R ≤ Real.log A at hm
  have hdiv := (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hm)
  simpa only [A, v, one_div, div_eq_mul_inv, mul_comm, mul_one] using hdiv

end ModifiedCartan
