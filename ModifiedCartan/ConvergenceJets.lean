import ModifiedCartan.Convergence
import ModifiedCartan.CauchyBounds

noncomputable section
set_option autoImplicit false
open Filter Metric Real Set
namespace ModifiedCartan

theorem compactConvergence_iteratedDeriv {g : ℕ → ℂ → ℂ} {s : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : CompactConvergence g s U)
    (hhol : ∀ n, DifferentiableOn ℂ (g n) U) (k : ℕ) :
    CompactConvergence (fun n => iteratedDeriv k (g n)) (iteratedDeriv k s) U := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    exact compactConvergence_deriv hU ih
      (fun n => (iteratedDeriv_analyticOnNhd ((hhol n).analyticOnNhd hU) k).differentiableOn)

/-- One nonnegative logarithmic bound controls every derivative through the
fixed finite order, including all initial terms of the convergent sequence. -/
theorem compactConvergence_jet_bound {g : ℕ → ℂ → ℂ} {s : ℂ → ℂ} {U Q : Set ℂ}
    (hU : IsOpen U) (hg : CompactConvergence g s U)
    (hhol : ∀ n, DifferentiableOn ℂ (g n) U) (hQU : Q ⊆ U) (hQ : IsCompact Q) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n (k : Fin m) z, z ∈ Q → ‖iteratedDeriv (k : ℕ) (g n) z‖ ≤ Real.exp B := by
  classical
  have hbound : ∀ k : Fin m, ∃ C : ℝ, ∀ n z, z ∈ Q → ‖iteratedDeriv (k : ℕ) (g n) z‖ ≤ C := by
    intro k
    exact compactConvergence_locallyBounded (compactConvergence_iteratedDeriv hU hg hhol k)
      (fun n => (iteratedDeriv_analyticOnNhd ((hhol n).analyticOnNhd hU) k).continuousOn) Q hQU hQ
  choose C hC using hbound
  let D := 1 + ∑ k : Fin m, max (C k) 0
  have hD : 1 ≤ D := by
    have := Finset.sum_nonneg (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) => le_max_right (C k) 0)
    dsimp [D]
    linarith
  refine ⟨Real.log D, Real.log_nonneg hD, ?_⟩
  intro n k z hz
  rw [Real.exp_log (by linarith : 0 < D)]
  have hk : max (C k) 0 ≤ ∑ l : Fin m, max (C l) 0 :=
    Finset.single_le_sum (fun l _ => le_max_right (C l) 0) (Finset.mem_univ k)
  have hn := (hC k n z hz).trans (le_max_left (C k) 0)
  dsimp [D]
  linarith

end ModifiedCartan
