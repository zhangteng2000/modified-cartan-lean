import ModifiedCartan.UnitGrowth
import ModifiedCartan.PoissonEnvelope
import ModifiedCartan.CombinationNorm
import ModifiedCartan.ProximityLocal
import ModifiedCartan.AnalyticStatements

noncomputable section
set_option autoImplicit false
open Metric Set Real InnerProductSpace
namespace ModifiedCartan

theorem absorption_envelope_bounds {m : ℕ} {A a : Fin m → ℂ → ℂ}
    {ρ δ η C₀ : ℝ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1)
    (hδ : 0 < δ) (hδη : δ ≤ η) (hη : η ≤ 1 / 64) (hC : 0 ≤ C₀)
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1))
    (ha : ∀ i, ContinuousOn (a i) (closedBall (0 : ℂ) (4 * η)))
    (hdom : ∀ i z, ‖z‖ ≤ 4 * η → ‖a i z‖ ≤ ‖A i z‖)
    (hpoints : ∀ i, ∃ z ∈ disk δ, Real.log ‖A i z‖ ≤ C₀) :
    ∀ i, Real.log ‖A i 0‖ ≤ 8 * δ * unitGrowthMean A ρ + C₀ ∧
      diskSupNorm (a i) (4 * η) ≤ Real.exp (64 * η * unitGrowthMean A ρ + C₀) := by
  have hρ0 : 0 < ρ := by linarith
  have hη0 : 0 < η := hδ.trans_le hδη
  let u := fun i z => Real.log ‖A i z‖
  let v := fun z => maxWithZero (fun i => u i z)
  have hu : ∀ i, HarmonicOnNhd (u i) (closedBall (0 : ℂ) ρ) :=
    fun i => (unit_log_harmonic (hA i)).mono (closedBall_subset_ball hρ1)
  have hv : CircleIntegrable v 0 ρ := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hρ0]
    exact (continuousOn_maxWithZero (fun i => (hu i).continuousOn)).mono sphere_subset_closedBall
  have hest := poisson_envelope_pointwise hρ hδ hδη hη hC hu hv
    (fun z _ => maxWithZero_nonneg (fun i => u i z))
    (fun i z _ => le_maxWithZero (fun j => u j z) i) hpoints
  intro i
  refine ⟨(hest i).1, ?_⟩
  obtain ⟨z, hz, he⟩ := diskSupNorm_attained (by positivity : 0 ≤ 4 * η) (ha i)
  rw [he]
  have hzn : ‖z‖ ≤ 4 * η := by simpa using hz
  have hzunit : z ∈ disk 1 := closedBall_subset_ball (by linarith : 4 * η < 1) hz
  apply (hdom i z hzn).trans
  rw [← Real.exp_log (norm_pos_iff.mpr ((hA i).2 z hzunit))]
  exact Real.exp_le_exp.mpr ((hest i).2 z hzn)

theorem proximityMean_le_unitGrowthMean {m : ℕ} {A : Fin m → ℂ → ℂ} {f : ℂ → ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1)
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1))
    (hf : MeromorphicOn f (sphere (0 : ℂ) R)) (i : Fin m)
    (hdom : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ ‖A i z‖) :
    proximityMean f R ≤ unitGrowthMean A R := by
  let u := fun j z => Real.log ‖A j z‖
  let v := fun z => maxWithZero (fun j => u j z)
  have hc : ContinuousOn v (sphere (0 : ℂ) |R|) := by
    rw [abs_of_nonneg hR]
    exact (continuousOn_maxWithZero (fun j => (unit_log_harmonic (hA j)).continuousOn)).mono
      (sphere_subset_ball hR1)
  have hfi : CircleIntegrable (fun z => Real.posLog ‖f z‖) 0 R := by
    exact (show MeromorphicOn f (sphere (0 : ℂ) |R|) by simpa [abs_of_nonneg hR] using hf).circleIntegrable_posLog_norm
  change Real.circleAverage (fun z => Real.posLog ‖f z‖) 0 R ≤ Real.circleAverage v 0 R
  apply Real.circleAverage_mono hfi hc.circleIntegrable'
  intro z hz
  have hzR : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_nonneg hR] using hz
  apply (Real.posLog_le_posLog (norm_nonneg _) (hdom z hzR)).trans
  rw [Real.posLog_apply]
  exact max_le (maxWithZero_nonneg (fun j => u j z)) (le_maxWithZero (fun j => u j z) i)

end ModifiedCartan
