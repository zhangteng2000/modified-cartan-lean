import ModifiedCartan.LogPoisson

noncomputable section
set_option autoImplicit false
open Metric Set InnerProductSpace
namespace ModifiedCartan

def harnackPower (T a c : ℝ) : ℝ := ((T + a) / (T - a)) * ((T + c) / (T - c))

theorem harnackPower_pos {T a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haT : a < T) (hcT : c < T) : 0 < harnackPower T a c := by
  have hT : 0 < T := lt_of_le_of_lt ha haT
  exact mul_pos (div_pos (by linarith) (by linarith)) (div_pos (by linarith) (by linarith))

theorem zero_free_log_lower {Q : ℂ → ℂ} {T a c t : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (haT : a < T) (hcT : c < T)
    (hQ : AnalyticOnNhd ℂ Q (closedBall (0 : ℂ) T))
    (hnz : ∀ z ∈ closedBall (0 : ℂ) T, Q z ≠ 0)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) T, ‖Q z‖ ≤ 1)
    {w z : ℂ} (hw : ‖w‖ ≤ a) (hz : ‖z‖ ≤ c) (ht : 0 < t) (htQ : t ≤ ‖Q w‖) :
    harnackPower T a c * Real.log t ≤ Real.log ‖Q z‖ := by
  have hT : 0 < T := lt_of_le_of_lt ha haT
  let u : ℂ → ℝ := fun v => -Real.log ‖Q v‖
  have hu : HarmonicContOnCl u (ball (0 : ℂ) T) := by
    apply HarmonicOnNhd.harmonicContOnCl
    rw [closure_ball _ hT.ne']
    intro v hv
    exact ((hQ v hv).harmonicAt_log_norm (hnz v hv)).neg
  have huB : ∀ v ∈ sphere (0 : ℂ) T, 0 ≤ u v := by
    intro v hv
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hbound v (sphere_subset_closedBall hv)))
  have hwH := (harmonic_harnack_uniform hu huB ha haT (by simpa using hw)).1
  have hzH := (harmonic_harnack_uniform hu huB hc hcT (by simpa using hz)).2
  have hA : 0 < (T - a) / (T + a) := div_pos (by linarith) (by linarith)
  have hB : 0 < (T - c) / (T + c) := div_pos (by linarith) (by linarith)
  have hmul := (mul_le_mul_of_nonneg_left hzH hA.le).trans hwH
  have hlog := Real.log_le_log ht htQ
  have htotal : ((T - a) / (T + a) * ((T - c) / (T + c))) * u z ≤ -Real.log t := by
    dsimp [u] at hmul ⊢
    nlinarith only [hmul, hlog]
  have hdiv : u z ≤ -Real.log t / ((T - a) / (T + a) * ((T - c) / (T + c))) :=
    (le_div_iff₀ (mul_pos hA hB)).mpr (by simpa only [mul_comm] using htotal)
  have hid : -Real.log t / ((T - a) / (T + a) * ((T - c) / (T + c))) =
      -(harnackPower T a c * Real.log t) := by
    dsimp [harnackPower]
    field_simp
  rw [hid] at hdiv
  dsimp [u] at hdiv
  linarith

theorem power_bound_zero_count {t q : ℝ} {N : ℕ}
    (ht : 0 < t) (hq : 0 < q) (hq1 : q < 1) (hbound : t ≤ q ^ N) :
    (N : ℝ) ≤ (-Real.log t) / (-Real.log q) := by
  have hl := Real.log_le_log ht hbound
  rw [Real.log_pow] at hl
  apply (le_div_iff₀ (neg_pos.mpr (Real.log_neg hq hq1))).mpr
  nlinarith only [hl]

end ModifiedCartan
