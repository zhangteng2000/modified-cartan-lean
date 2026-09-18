import ModifiedCartan.Wronskian
import Mathlib.Analysis.Complex.Liouville

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

/-- Uniform Cauchy bounds on a fixed smaller closed disk. -/
theorem iteratedDeriv_unit_disk_bound {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hbound : ∀ z ∈ disk 1, ‖F z‖ ≤ 1)
    {r : ℝ} (hr : r < 1) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖iteratedDeriv n F z‖ ≤ (n.factorial : ℝ) / ((1 - r) / 2) ^ n := by
  have hrad : 0 < (1 - r) / 2 := by linarith
  have hsub : closedBall z ((1 - r) / 2) ⊆ disk 1 := by
    intro w hw
    have hdist : ‖w - z‖ ≤ (1 - r) / 2 := by simpa [mem_closedBall, dist_eq_norm] using hw
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      calc
        _ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    change dist w 0 < 1
    rw [dist_zero_right]
    linarith
  have hd : DifferentiableOn ℂ F (closure (ball z ((1 - r) / 2))) := by
    rw [closure_ball _ hrad.ne']
    exact hF.mono hsub
  simpa only [mul_one] using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hrad hd.diffContOnCl (fun w hw => hbound w (hsub (sphere_subset_closedBall hw)))

/-- The derivative jets used in the Wronskian are analytic. -/
theorem iteratedDeriv_analyticOnNhd {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (n : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv n F) U := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

theorem wronskian_analyticOnNhd {m : ℕ} {g : Fin m → ℂ → ℂ} {U : Set ℂ}
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) : AnalyticOnNhd ℂ (wronskian g) U := by
  intro z hz
  unfold wronskian
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact iteratedDeriv_analyticOnNhd (hg i) (σ i) z hz

/-- An explicit entrywise determinant bound, used for the Wronskian and its minors. -/
theorem matrix_det_norm_bound {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {B : ℝ}
    (_hB : 0 ≤ B) (hM : ∀ i j, ‖M i j‖ ≤ B) :
    ‖M.det‖ ≤ (m.factorial : ℝ) * B ^ m := by
  classical
  rw [Matrix.det_apply']
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin m), B ^ m := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, norm_prod]
      have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [hsign, one_mul]
      calc
        _ ≤ ∏ _i : Fin m, B := Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hM _ _)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

def wronskianUpperBound (m : ℕ) (r : ℝ) : ℝ :=
  (m.factorial : ℝ) * (1 + ∑ i : Fin m, ((i : ℕ).factorial : ℝ) / ((1 - r) / 2) ^ (i : ℕ)) ^ m

theorem wronskianUpperBound_pos (m : ℕ) {r : ℝ} (hr : r < 1) :
    0 < wronskianUpperBound m r := by
  have hrad : 0 < (1 - r) / 2 := by linarith
  apply mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos m))
  apply pow_pos
  have : 0 ≤ ∑ i : Fin m, ((i : ℕ).factorial : ℝ) / ((1 - r) / 2) ^ (i : ℕ) :=
    Finset.sum_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg hrad.le _))
  linarith

theorem wronskian_unit_disk_bound {m : ℕ} {g : Fin m → ℂ → ℂ}
    (hg : ∀ j, DifferentiableOn ℂ (g j) (disk 1))
    (hbound : ∀ j z, z ∈ disk 1 → ‖g j z‖ ≤ 1)
    {r : ℝ} (hr : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖wronskian g z‖ ≤ wronskianUpperBound m r := by
  have hrad : 0 < (1 - r) / 2 := by linarith
  have hpos : ∀ i : Fin m, 0 ≤ ((i : ℕ).factorial : ℝ) / ((1 - r) / 2) ^ (i : ℕ) :=
    fun i => div_nonneg (Nat.cast_nonneg _) (pow_nonneg hrad.le _)
  apply matrix_det_norm_bound
  · have := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hpos i)
    linarith
  · intro i j
    have hi := iteratedDeriv_unit_disk_bound (hg j) (hbound j) hr (i : ℕ) hz
    have hsum := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hpos i)
      (Finset.mem_univ i)
    exact hi.trans (by linarith)

end ModifiedCartan
