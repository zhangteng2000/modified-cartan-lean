import ModifiedCartan.UnitGrowth
import ModifiedCartan.PoissonHarnack

noncomputable section
set_option autoImplicit false
open Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

def unitEnvelope {m : ℕ} (A : Fin m → ℂ → ℂ) (R : ℝ) (z : ℂ) : ℝ :=
  poissonExtension (fun w => maxWithZero (fun i => Real.log ‖A i w‖)) R z

theorem unitEnvelope_integrable {m : ℕ} {A : Fin m → ℂ → ℂ} {R : ℝ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) (hR : 0 ≤ R) (hR1 : R < 1) :
    CircleIntegrable (fun w => maxWithZero (fun i => Real.log ‖A i w‖)) 0 R := by
  apply ContinuousOn.circleIntegrable'
  rw [abs_of_nonneg hR]
  exact (continuousOn_maxWithZero (fun i => (unit_log_harmonic (hA i)).continuousOn)).mono
    (sphere_subset_ball hR1)

theorem unitEnvelope_harmonic {m : ℕ} {A : Fin m → ℂ → ℂ} {R : ℝ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) (hR : 0 ≤ R) (hR1 : R < 1) :
    HarmonicOnNhd (unitEnvelope A R) (disk R) :=
  poissonExtension_harmonic (unitEnvelope_integrable hA hR hR1)

theorem unitEnvelope_zero {m : ℕ} {A : Fin m → ℂ → ℂ} {R : ℝ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) (hR : 0 < R) (hR1 : R < 1) :
    unitEnvelope A R 0 = unitGrowthMean A R :=
  poissonExtension_zero hR (unitEnvelope_integrable hA hR.le hR1)

theorem unitEnvelope_dominates {m : ℕ} {A : Fin m → ℂ → ℂ} {R : ℝ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) (hR : 0 < R) (hR1 : R < 1)
    {z : ℂ} (hz : z ∈ disk R) :
    0 ≤ unitEnvelope A R z ∧ ∀ i, Real.log ‖A i z‖ ≤ unitEnvelope A R z := by
  have hmax := harmonic_max_le_poissonExtension hR
    (fun i => (unit_log_harmonic (hA i)).mono (closedBall_subset_ball hR1)) hz
  exact ⟨(maxWithZero_nonneg _).trans hmax, fun i => (le_maxWithZero _ i).trans hmax⟩

theorem unitEnvelope_positive {m : ℕ} {A : Fin m → ℂ → ℂ} {R : ℝ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) (hR : 0 < R) (hR1 : R < 1)
    (hM : 0 < unitGrowthMean A R) {z : ℂ} (hz : z ∈ disk R) : 0 < unitEnvelope A R z := by
  have hbound := (poissonExtension_harnack_bounds (unitEnvelope_integrable hA hR.le hR1)
    (fun _ _ => maxWithZero_nonneg _) hz).1
  rw [poissonExtension_zero hR (unitEnvelope_integrable hA hR.le hR1)] at hbound
  have hzn : ‖z‖ < R := by simpa [disk] using hz
  exact (mul_pos (div_pos (sub_pos.mpr hzn) (by positivity)) hM).trans_le hbound

theorem unitEnvelope_deficit_harmonic {m : ℕ} {A : Fin m → ℂ → ℂ} {R : ℝ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) (hR : 0 ≤ R) (hR1 : R < 1) (i : Fin m) :
    HarmonicOnNhd (fun z => unitEnvelope A R z - Real.log ‖A i z‖) (disk R) :=
  (unitEnvelope_harmonic hA hR hR1).sub ((unit_log_harmonic (hA i)).mono (ball_subset_ball hR1.le))

end ModifiedCartan
