import ModifiedCartan.LogNormPaths
import ModifiedCartan.ReciprocalProximity

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- Each zero-free circle with bounded logarithmic derivative admits one of
two uniform modulus bounds, with the same constant on every point of that circle. -/
theorem circle_logDerivative_alternative {f : ℂ → ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ∀ z ∈ sphere (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hn : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖logDeriv f z‖ ≤ C) :
    (∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ Real.exp (2*Real.pi*R*C)) ∨
      ∀ z ∈ sphere (0 : ℂ) R, ‖(f z)⁻¹‖ ≤ Real.exp (2*Real.pi*R*C) := by
  have hbase : (R : ℂ) ∈ sphere (0 : ℂ) R := by simp [abs_of_pos hR]
  by_cases hsmall : ‖f (R : ℂ)‖ ≤ 1
  · left
    intro z hz
    have hv := circle_log_norm_variation hR hC hf hn hb hz
    have hlog := Real.log_nonpos (norm_nonneg (f (R : ℂ))) hsmall
    have hle := le_abs_self (Real.log ‖f z‖ - Real.log ‖f (R : ℂ)‖)
    apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hn z hz))).mp
    linarith
  · right
    intro z hz
    have hv := circle_log_norm_variation hR hC hf hn hb hz
    have hlog := Real.log_nonneg (le_of_not_ge hsmall)
    have hle := neg_le_abs (Real.log ‖f z‖ - Real.log ‖f (R : ℂ)‖)
    have hp : 0 < ‖(f z)⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero (hn z hz))
    apply (Real.log_le_iff_le_exp hp).mp
    rw [norm_inv,Real.log_inv]
    linarith

theorem proximityMean_le_of_circle_exp {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hf : MeromorphicOn f (sphere (0 : ℂ) |R|))
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ Real.exp B) :
    proximityMean f R ≤ B := by
  have hpoint : ∀ z ∈ sphere (0 : ℂ) |R|, Real.posLog ‖f z‖ ≤ B := by
    intro z hz
    have hz' : z ∈ sphere (0 : ℂ) R := by simpa only [abs_of_nonneg hR] using hz
    rw [Real.posLog_apply]
    apply max_le hB
    by_cases hn : f z = 0
    · simpa only [hn,norm_zero,Real.log_zero] using hB
    · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hn)).mpr (hb z hz')
  have h := Real.circleAverage_mono hf.circleIntegrable_posLog_norm
    (circleIntegrable_const B 0 R) hpoint
  simpa only [proximityMean,ValueDistribution.proximity_top,Real.circleAverage_const] using h

/-- The circle alternative gives one bounded proximity mean. It allows the
chosen side to vary between radii, as required by the Cartan argument. -/
theorem circle_logDerivative_proximity_alternative {f : ℂ → ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hm : MeromorphicOn f (sphere (0 : ℂ) |R|))
    (hf : ∀ z ∈ sphere (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hn : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖logDeriv f z‖ ≤ C) :
    proximityMean f R ≤ 2*Real.pi*R*C ∨
      proximityMean (fun z => (f z)⁻¹) R ≤ 2*Real.pi*R*C := by
  have hc : 0 ≤ 2*Real.pi*R*C := by positivity
  rcases circle_logDerivative_alternative hR hC hf hn hb with h | h
  · exact Or.inl (proximityMean_le_of_circle_exp hR.le hc hm h)
  · exact Or.inr (proximityMean_le_of_circle_exp hR.le hc hm.inv h)

end ModifiedCartan
