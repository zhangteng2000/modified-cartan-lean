import ModifiedCartan.Convergence

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem compactConvergence_eval_zero {f : ℕ → ℂ → ℂ} {U K : Set ℂ} {z : ℕ → ℂ}
    (hf : CompactConvergence f 0 U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hz : ∀ᶠ n in atTop, z n ∈ K) : Tendsto (fun n => f n (z n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hf K hKU hK) ε hε, hz] with n hn hzn
  simpa only [Pi.zero_apply, dist_comm] using hn (z n) hzn

theorem tendsto_zero_of_small_ratio_bounded_log {a A : ℕ → ℂ} {C : ℝ}
    (hsmall : Tendsto (fun n => a n / A n) atTop (𝓝 0))
    (hA : ∀ᶠ n in atTop, A n ≠ 0 ∧ Real.log ‖A n‖ ≤ C) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun n => ‖a n / A n‖ * Real.exp C) atTop (𝓝 0) := by
    simpa only [norm_zero, zero_mul] using hsmall.norm.mul_const (Real.exp C)
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg (a n))) ?_ hlim
  filter_upwards [hA] with n hn
  have hnormA : ‖A n‖ ≤ Real.exp C := (Real.log_le_iff_le_exp (norm_pos_iff.mpr hn.1)).mp hn.2
  calc
    _ = ‖a n / A n‖ * ‖A n‖ := by rw [← norm_mul, div_mul_cancel₀ _ hn.1]
    _ ≤ _ := mul_le_mul_of_nonneg_left hnormA (norm_nonneg _)

theorem quotient_tendsto_zero_of_norm_lower {a s : ℕ → ℂ} {c : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hc : 0 < c) (hs : ∀ᶠ n in atTop, c ≤ ‖s n‖) :
    Tendsto (fun n => a n / s n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun n => ‖a n‖ / c) atTop (𝓝 0) := by
    simpa only [norm_zero, zero_div] using ha.norm.div_const c
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg (a n / s n))) ?_ hlim
  filter_upwards [hs] with n hn
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hc hn

end ModifiedCartan
