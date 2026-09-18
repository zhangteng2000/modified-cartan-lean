import ModifiedCartan.HolomorphicLog
import ModifiedCartan.RealPartCauchy
import ModifiedCartan.ZeroFreeGrowth

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

/-- Explicit higher derivative bounds for a holomorphic logarithm of the
zero-free remainder, derived from an off-center lower bound. -/
theorem zero_free_log_derivatives {Q : ℂ → ℂ} {T α H τ r : ℝ}
    (hα : 0 ≤ α) (hαT : α < T) (hH : 1 ≤ H) (hr : 0 ≤ r) (hrT : r < T)
    (hQ : AnalyticOnNhd ℂ Q (closedBall (0 : ℂ) T))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) T, Q z ≠ 0)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) T, ‖Q z‖ ≤ Real.exp H)
    {w : ℂ} (hw : ‖w‖ ≤ α) (hτ : 0 < τ) (hτQ : τ ≤ ‖Q w‖) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (disk T) ∧
      (∀ z ∈ disk T, Complex.exp (L z) = Q z) ∧
      (∀ z ∈ disk T, deriv L z = logDeriv Q z) ∧
      ∀ (j : ℕ), 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ r →
        ‖iteratedDeriv j L z‖ ≤ (j.factorial : ℝ) / ((T - r) / 2) ^ j *
          (2 * ((1 + (T + α) / (T - α)) * (H + Real.posLog (1 / τ))) *
            ((T + r) / 2) / (T - (T + r) / 2)) := by
  have hT : 0 < T := hα.trans_lt hαT
  obtain ⟨L, hL, _hL0, hexp, hder⟩ := exists_holomorphic_log_on_disk hT
    (hQ.differentiableOn.mono ball_subset_closedBall) (fun z hz => hnz z (ball_subset_closedBall hz))
  refine ⟨L, hL, hexp, hder, ?_⟩
  let E := H + Real.posLog (1 / τ)
  let C := 1 + (T + α) / (T - α)
  have hE : 0 < E := by
    dsimp [E]
    have hp : 0 ≤ Real.posLog (1 / τ) := Real.posLog_nonneg
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hdef := zero_free_log_deficit_at_origin hα hαT hQ hnz hbound hw hτ hτQ
  have hz0 : (0 : ℂ) ∈ disk T := by simpa [disk]
  let f : ℂ → ℂ := fun z => -L 0 + L z
  have hf : DifferentiableOn ℂ f (disk T) := hL.const_add _
  have hf0 : f 0 = 0 := by simp [f]
  have hre : ∀ z ∈ disk T, (f z).re ≤ C * E := by
    intro z hz
    have hlog := Real.log_le_log (norm_pos_iff.mpr (hnz z (ball_subset_closedBall hz)))
      (hbound z (ball_subset_closedBall hz))
    rw [Real.log_exp] at hlog
    dsimp [f]
    rw [holomorphic_log_real_part hexp hz0,
      holomorphic_log_real_part hexp hz]
    dsimp [C, E] at *
    nlinarith only [hlog, hdef, hE]
  intro j hj z hz
  have hest := iteratedDeriv_bound_of_real_part hr hrT (mul_pos hC hE) hf hf0 hre j hz
  change ‖iteratedDeriv j (fun z => -L 0 + L z) z‖ ≤ _ at hest
  rw [iteratedDeriv_const_add (by omega) (-L 0)] at hest
  exact hest

end ModifiedCartan
