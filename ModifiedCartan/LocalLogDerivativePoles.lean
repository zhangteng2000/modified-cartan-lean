import ModifiedCartan.ZeroCount
import ModifiedCartan.ZeroFreeLogDerivatives
import ModifiedCartan.FinitePoleBounds
import ModifiedCartan.ProximityGrowth
import ModifiedCartan.CombinationNorm

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

/-- The actual local factorization gives all logarithmic derivative pole bounds
at once, without excluding zeros on either auxiliary circle. -/
theorem local_log_derivative_poles {F : ℂ → ℂ} {α r₀ r R τ : ℝ}
    (hα : 0 < α) (hαr : α < r₀) (hr₀ : r₀ ≤ r) (hrR : r < R) (hR : R < 1)
    (hF : DifferentiableOn ℂ F (disk 1)) (hτ : 0 < τ) (hτF : τ ≤ diskSupNorm F α) :
    let S := (r + R) / 2
    let T := (3 * r + R) / 4
    let E := 1 + 4 * proximityMean F R / (R - r) + Real.posLog (1 / τ)
    ∃ (s : Finset ℂ) (m : ℂ → ℕ),
      ((∑ a ∈ s, m a : ℕ) : ℝ) ≤ E / (blaschkeDecayConstant r₀ α * ((R - r) / 4)) ∧
      ∀ n : ℕ, ∀ z : ℂ, ‖z‖ ≤ r → z ∉ s →
        ‖iteratedDeriv n (logDeriv F) z‖ ≤
          (∑ a ∈ s, (m a : ℝ) * ((n.factorial : ℝ) * ‖z - a‖ ^ (-1 - (n : ℤ)))) +
          ((∑ a ∈ s, m a : ℕ) : ℝ) *
            ((n.factorial : ℝ) * (2 / (S - r)) / ((S - r) / 2) ^ n) +
          ((n + 1).factorial : ℝ) / ((T - r) / 2) ^ (n + 1) *
            (2 * ((1 + (T + α) / (T - α)) * E) * ((T + r) / 2) / (T - (T + r) / 2)) := by
  dsimp only
  let S := (r + R) / 2
  let T := (3 * r + R) / 4
  let H := 1 + 4 * proximityMean F R / (R - r)
  have hr : 0 < r := hα.trans (hαr.trans_le hr₀)
  have hSR : S < R := by dsimp [S]; linarith
  have hS : 0 < S := by dsimp [S]; linarith
  have hT : 0 < T := by dsimp [T]; linarith
  have hrT : r < T := by dsimp [T]; linarith
  have hTS : T < S := by dsimp [T, S]; linarith
  have hαT : α < T := hαr.trans_le hr₀ |>.trans hrT
  have hA := hF.analyticOnNhd isOpen_ball
  have hAR : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R) :=
    hA.mono (closedBall_subset_ball hR)
  have hAα : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) α) :=
    hA.mono (closedBall_subset_ball (hαr.trans_le hr₀ |>.trans (hrR.trans hR)))
  obtain ⟨w, hw, hmax⟩ := diskSupNorm_attained hα.le hAα.continuousOn
  have hτw : τ ≤ ‖F w‖ := by rwa [hmax] at hτF
  have hwnorm : ‖w‖ ≤ α := by simpa using hw
  have hH : 1 ≤ H := by
    dsimp [H]
    have hm : 0 ≤ proximityMean F R := ValueDistribution.proximity_nonneg R
    have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hm) (sub_pos.mpr hrR).le
    linarith
  have hb : ∀ z ∈ sphere (0 : ℂ) S, ‖F z‖ ≤ Real.exp H := by
    intro z hz
    exact norm_le_exp_proximity_midpoint hr.le hrR hR.le hAR (by simpa [S] using hz.le)
  obtain ⟨s, m, Q, hs, hQ, hQnz, hQbound, hfact, hN⟩ :=
    blaschke_factorization_zero_count hF hb hα.le hαr (by dsimp [S]; linarith)
      (hSR.trans hR) hT.le (show 0 < (R - r) / 4 by linarith)
      (show T + (R - r) / 4 ≤ S by dsimp [T, S]; linarith) hwnorm hτ hτw
  have hwS : w ∈ closedBall (0 : ℂ) S := by simpa using hwnorm.trans (hαT.trans hTS).le
  have hτQ : τ ≤ ‖Q w‖ := by
    apply hτw.trans
    rw [hfact w hwS, norm_mul]
    have hp : ‖∏ a ∈ s, blaschkeFactor S a w ^ m a‖ ≤ 1 := by
      simp only [norm_prod, norm_pow]
      apply Finset.prod_le_one (fun a _ => pow_nonneg (norm_nonneg _) _)
      intro a ha
      exact pow_le_one₀ (norm_nonneg _) (blaschkeFactor_norm_le_one hS
        ((hs a ha).1.trans_lt hTS) (by simpa using hwS))
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _)
  have hQT : AnalyticOnNhd ℂ Q (closedBall (0 : ℂ) T) :=
    hQ.mono (closedBall_subset_ball (hTS.trans (hSR.trans hR)))
  obtain ⟨L, _hL, _hexp, hder, hLbound⟩ := zero_free_log_derivatives hα.le hαT hH hr.le hrT
    hQT hQnz (fun z hz => hQbound z (closedBall_subset_closedBall hTS.le hz)) hwnorm hτ hτQ
  refine ⟨s, m, hN, ?_⟩
  intro n z hz hzs
  have hpole := finite_pole_derivative_bound s m hr.le hrT hTS
    (fun a ha => (hs a ha).1) hQT hQnz hfact n hz hzs
  rw [iterated_logDeriv_eq_log_branch isOpen_ball hder n
    (show z ∈ disk T by simpa [disk] using hz.trans_lt hrT)] at hpole
  exact hpole.trans (add_le_add le_rfl (hLbound (n + 1) (by omega) z hz))

end ModifiedCartan
