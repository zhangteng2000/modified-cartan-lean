import ModifiedCartan.CauchyBounds
import ModifiedCartan.AnalyticStatements
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

noncomputable section
set_option autoImplicit false
open Metric Set Real
namespace ModifiedCartan

theorem matrix_det_norm_column_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Fin m → ℝ) (_hB : ∀ j, 0 ≤ B j) (hA : ∀ i j, ‖A i j‖ ≤ B j) :
    ‖A.det‖ ≤ (m.factorial : ℝ) * ∏ j, B j := by
  classical
  rw [Matrix.det_apply']
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), ∏ j, B j := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_mul, norm_prod]
      have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [hsign, one_mul]
      exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hA _ _)
    _ = _ := by simp [Fintype.card_perm]

/-- Replacing any chosen column by the sum of all columns leaves the Wronskian unchanged. -/
theorem wronskian_update_sum {m : ℕ} {a : Fin m → ℂ → ℂ} {z : ℂ}
    (ha : ∀ i, AnalyticAt ℂ (a i) z) (j : Fin m) :
    wronskian (Function.update a j (fun w => ∑ i, a i w)) z = wronskian a z := by
  classical
  let A : Matrix (Fin m) (Fin m) ℂ := .of fun k i => iteratedDeriv (k : ℕ) (a i) z
  have hmatrix : (.of fun k i : Fin m =>
      iteratedDeriv (k : ℕ) (Function.update a j (fun w => ∑ l, a l w) i) z) =
      A.updateCol j (fun k => ∑ i, (1 : ℂ) • A k i) := by
    ext k i
    by_cases hij : i = j
    · subst i
      simpa [A, Function.update] using
        (iteratedDeriv_fun_sum (n := (k : ℕ)) (I := Finset.univ) (fun l _ => (ha l).contDiffAt))
    · simp [hij, A]
  unfold wronskian
  rw [hmatrix, Matrix.det_updateCol_sum]
  simp only [one_smul]
  rfl

def derivativeColumnError {m : ℕ} (a : ℂ → ℂ) (z : ℂ) : ℝ :=
  ∑ k : Fin m, Real.posLog ‖iteratedDeriv (k : ℕ) a z / a z‖

theorem derivativeColumnError_nonneg {m : ℕ} (a : ℂ → ℂ) (z : ℂ) :
    0 ≤ derivativeColumnError (m := m) a z :=
  Finset.sum_nonneg (fun _ _ => Real.posLog_nonneg)

theorem derivative_norm_le_column_exp {m : ℕ} (a : ℂ → ℂ) {A z : ℂ}
    (ha : a z ≠ 0) (hA : A ≠ 0) (hbound : ‖a z‖ ≤ ‖A‖) (k : Fin m) :
    ‖iteratedDeriv (k : ℕ) a z‖ ≤
      Real.exp (Real.log ‖A‖ + derivativeColumnError (m := m) a z) := by
  have hlog : Real.posLog ‖iteratedDeriv (k : ℕ) a z / a z‖ ≤ derivativeColumnError (m := m) a z := by
    unfold derivativeColumnError
    exact Finset.single_le_sum (f := fun i : Fin m => Real.posLog ‖iteratedDeriv (i : ℕ) a z / a z‖)
      (fun i _ => Real.posLog_nonneg) (Finset.mem_univ k)
  have hratio : ‖iteratedDeriv (k : ℕ) a z / a z‖ ≤
      Real.exp (derivativeColumnError (m := m) a z) := by
    by_cases hz : iteratedDeriv (k : ℕ) a z / a z = 0
    · simp only [hz, norm_zero]
      exact (Real.exp_pos _).le
    · rw [← Real.exp_log (norm_pos_iff.mpr hz)]
      apply Real.exp_le_exp.mpr
      exact (show Real.log ‖iteratedDeriv (k : ℕ) a z / a z‖ ≤
        Real.posLog ‖iteratedDeriv (k : ℕ) a z / a z‖ by simp [Real.posLog_apply]).trans hlog
  calc
    _ = ‖iteratedDeriv (k : ℕ) a z / a z‖ * ‖a z‖ := by
      rw [← norm_mul, div_mul_cancel₀ _ ha]
    _ ≤ Real.exp (derivativeColumnError (m := m) a z) * ‖A‖ :=
      mul_le_mul hratio hbound (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr hA)]; ring

/-- The pointwise boundary estimate after replacing a chosen column by the sum.
Zeros are excluded only at this point; the integrated version removes them by
the codiscrete exceptional-set theorem. -/
theorem wronskian_boundary_log_bound {m : ℕ} {a : Fin m → ℂ → ℂ} {A : Fin m → ℂ}
    {z : ℂ} {B : ℝ} (ha : ∀ i, AnalyticAt ℂ (a i) z)
    (han : ∀ i, a i z ≠ 0) (hAn : ∀ i, A i ≠ 0)
    (hdom : ∀ i, ‖a i z‖ ≤ ‖A i‖)
    (hsum : ∀ k : Fin m, ‖iteratedDeriv (k : ℕ) (fun w => ∑ i, a i w) z‖ ≤ Real.exp B)
    (hW : wronskian a z ≠ 0) (j : Fin m) :
    Real.log ‖wronskian a z‖ ≤ (∑ i, Real.log ‖A i‖) - Real.log ‖A j‖ +
      (Real.log (m.factorial : ℝ) + B + ∑ i, derivativeColumnError (m := m) (a i) z) := by
  classical
  let b := Function.update a j (fun w => ∑ i, a i w)
  let e : Fin m → ℝ := fun i => if i = j then B else Real.log ‖A i‖ + derivativeColumnError (m := m) (a i) z
  let Y : Matrix (Fin m) (Fin m) ℂ := .of fun k i => iteratedDeriv (k : ℕ) (b i) z
  have hentry : ∀ k i, ‖Y k i‖ ≤ Real.exp (e i) := by
    intro k i
    by_cases hij : i = j
    · subst i
      simpa [Y, b, e] using hsum k
    · simpa [Y, b, e, Function.update_of_ne hij, hij] using
        derivative_norm_le_column_exp (a i) (han i) (hAn i) (hdom i) k
  have hdet := matrix_det_norm_column_bound Y (fun i => Real.exp (e i))
    (fun i => (Real.exp_pos _).le) hentry
  have hY : Y.det = wronskian a z := wronskian_update_sum ha j
  rw [hY, ← Real.exp_sum] at hdet
  have hf : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hexp : ‖wronskian a z‖ ≤ Real.exp (Real.log (m.factorial : ℝ) + ∑ i, e i) := by
    simpa only [Real.exp_add, Real.exp_log hf] using hdet
  have hlog := (Real.log_le_iff_le_exp (norm_pos_iff.mpr hW)).mpr hexp
  apply hlog.trans
  have he : (∑ i, e i) = B + ∑ i ∈ Finset.univ.erase j,
      (Real.log ‖A i‖ + derivativeColumnError (m := m) (a i) z) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [e, ite_eq_left rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.mem_erase.mp hi).1]
  have hlogs := Finset.add_sum_erase Finset.univ (fun i => Real.log ‖A i‖) (Finset.mem_univ j)
  have herr := Finset.add_sum_erase Finset.univ
    (fun i => derivativeColumnError (m := m) (a i) z) (Finset.mem_univ j)
  rw [he, Finset.sum_add_distrib]
  linarith [derivativeColumnError_nonneg (m := m) (a j) z]

end ModifiedCartan
