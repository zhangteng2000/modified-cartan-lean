import ModifiedCartan.BlaschkeDecomposition
import ModifiedCartan.BlaschkeQuantitative

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

/-- The quantitative zero count used for logarithmic derivatives, together with
the actual finite factorization and its zero-free remainder. -/
theorem blaschke_factorization_zero_count {F : ℂ → ℂ} {r₀ α S T d H τ : ℝ} {w : ℂ}
    (hF : DifferentiableOn ℂ F (disk 1))
    (hbound : ∀ z ∈ sphere (0 : ℂ) S, ‖F z‖ ≤ Real.exp H)
    (hα : 0 ≤ α) (hαr : α < r₀) (hrS : r₀ ≤ S) (hS1 : S < 1)
    (hT : 0 ≤ T) (hd : 0 < d) (hTd : T + d ≤ S)
    (hw : ‖w‖ ≤ α) (hτ : 0 < τ) (hτF : τ ≤ ‖F w‖) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ) (Q : ℂ → ℂ),
      (∀ a ∈ s, ‖a‖ ≤ T ∧ 0 < m a) ∧
      AnalyticOnNhd ℂ Q (disk 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) T, Q z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) S, ‖Q z‖ ≤ Real.exp H) ∧
      (∀ z ∈ closedBall (0 : ℂ) S, F z = (∏ a ∈ s, blaschkeFactor S a z ^ m a) * Q z) ∧
      ((∑ a ∈ s, m a : ℕ) : ℝ) ≤
        (H + Real.posLog (1 / τ)) / (blaschkeDecayConstant r₀ α * d) := by
  have hwS : w ∈ closedBall (0 : ℂ) S := by
    simpa using hw.trans (hαr.le.trans hrS)
  have hwunit : w ∈ disk 1 := closedBall_subset_ball hS1 hwS
  have hFw : F w ≠ 0 := norm_pos_iff.mp (hτ.trans_le hτF)
  obtain ⟨s, m, Q, hs, hQ, hQnz, hQbound, hfact⟩ :=
    bounded_blaschke_factorization_local hF hbound hwunit hFw hT (by linarith) hS1
  refine ⟨s, m, Q, hs, hQ, hQnz, hQbound, hfact, ?_⟩
  let N := ∑ a ∈ s, m a
  let c := blaschkeDecayConstant r₀ α
  let q := Real.exp (-(c * d))
  have hc : 0 < c := blaschkeDecayConstant_pos hα hαr
  have hprod : ‖∏ a ∈ s, blaschkeFactor S a w ^ m a‖ ≤ q ^ N := by
    simp only [norm_prod, norm_pow]
    dsimp [N]
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _)
    intro a ha
    exact pow_le_pow_left₀ (norm_nonneg _)
      (blaschkeFactor_exponential_bound hα hαr hrS hS1.le hd hTd (hs a ha).1 hw) _
  have hτbound : τ ≤ q ^ N * Real.exp H := by
    apply hτF.trans
    rw [hfact w hwS, norm_mul]
    exact mul_le_mul hprod (hQbound w hwS) (norm_nonneg _) (pow_nonneg (Real.exp_pos _).le _)
  have hlog := Real.log_le_log hτ hτbound
  rw [Real.log_mul (pow_ne_zero _ (Real.exp_pos _).ne') (Real.exp_pos H).ne',
    Real.log_pow] at hlog
  simp only [Real.log_exp] at hlog
  have hpos : -Real.log τ ≤ Real.posLog (1 / τ) := by
    simp only [one_div, Real.posLog_apply, Real.log_inv]
    exact le_max_right _ _
  change (N : ℝ) ≤ _
  apply (le_div_iff₀ (mul_pos hc hd)).mpr
  nlinarith only [hlog, hpos]

end ModifiedCartan
