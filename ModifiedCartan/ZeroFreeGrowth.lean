import ModifiedCartan.CartanAux

noncomputable section
set_option autoImplicit false
open Metric Set InnerProductSpace
namespace ModifiedCartan

theorem zero_free_log_deficit_at_origin {Q : ℂ → ℂ} {T α H τ : ℝ}
    (hα : 0 ≤ α) (hαT : α < T)
    (hQ : AnalyticOnNhd ℂ Q (closedBall (0 : ℂ) T))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) T, Q z ≠ 0)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) T, ‖Q z‖ ≤ Real.exp H)
    {w : ℂ} (hw : ‖w‖ ≤ α) (hτ : 0 < τ) (hτQ : τ ≤ ‖Q w‖) :
    H - Real.log ‖Q 0‖ ≤ (T + α) / (T - α) * (H + Real.posLog (1 / τ)) := by
  have hT : 0 < T := hα.trans_lt hαT
  let u : ℂ → ℝ := fun z => H - Real.log ‖Q z‖
  have hu : HarmonicContOnCl u (ball (0 : ℂ) T) := by
    apply HarmonicOnNhd.harmonicContOnCl
    rw [closure_ball _ hT.ne']
    intro z hz
    exact (harmonicAt_const H).sub ((hQ z hz).harmonicAt_log_norm (hnz z hz))
  have hub : ∀ z ∈ sphere (0 : ℂ) T, 0 ≤ u z := by
    intro z hz
    have hlog := Real.log_le_log (norm_pos_iff.mpr (hnz z (sphere_subset_closedBall hz)))
      (hbound z (sphere_subset_closedBall hz))
    rw [Real.log_exp] at hlog
    exact sub_nonneg.mpr hlog
  have hh := (harmonic_harnack_uniform hu hub hα hαT (by simpa using hw)).1
  have hlog := Real.log_le_log hτ hτQ
  have hpos : -Real.log τ ≤ Real.posLog (1 / τ) := by
    simp only [one_div, Real.posLog_apply, Real.log_inv]
    exact le_max_right _ _
  have ha : 0 < (T - α) / (T + α) := div_pos (by linarith) (by linarith)
  have htotal : (T - α) / (T + α) * u 0 ≤ H + Real.posLog (1 / τ) := by
    dsimp [u] at hh ⊢
    linarith
  have hdiv : u 0 ≤ (H + Real.posLog (1 / τ)) / ((T - α) / (T + α)) :=
    (le_div_iff₀ ha).mpr (by simpa [mul_comm] using htotal)
  dsimp [u] at hdiv
  convert hdiv using 1
  field_simp

end ModifiedCartan
