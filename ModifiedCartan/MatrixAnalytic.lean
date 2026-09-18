import ModifiedCartan.CauchyBounds
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

theorem matrix_det_analyticAt {m : ℕ} {M : ℂ → Matrix (Fin m) (Fin m) ℂ} {z : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) :
    AnalyticAt ℂ (fun w => (M w).det) z := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  exact Finset.analyticAt_fun_prod _ (fun i _ => hM (σ i) i)

theorem matrix_adjugate_entry_analyticAt {m : ℕ} {M : ℂ → Matrix (Fin m) (Fin m) ℂ} {z : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) (i j : Fin m) :
    AnalyticAt ℂ (fun w => (M w).adjugate i j) z := by
  classical
  simp only [Matrix.adjugate_apply]
  apply matrix_det_analyticAt
  intro k l
  by_cases hkj : k = j
  · subst k
    simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (Pi.single i 1 : Fin m → ℂ) l) z)
  · simpa [Matrix.updateRow_apply, hkj] using hM k l

theorem matrix_inv_entry_analyticAt {m : ℕ} {M : ℂ → Matrix (Fin m) (Fin m) ℂ} {z : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) (hdet : (M z).det ≠ 0) (i j : Fin m) :
    AnalyticAt ℂ (fun w => (M w)⁻¹ i j) z := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((matrix_det_analyticAt hM).inv hdet).mul (matrix_adjugate_entry_analyticAt hM i j)

theorem matrix_adjugate_norm_bound {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {B : ℝ}
    (hB : 1 ≤ B) (hM : ∀ i j, ‖M i j‖ ≤ B) (i j : Fin m) :
    ‖M.adjugate i j‖ ≤ (m.factorial : ℝ) * B ^ m := by
  classical
  rw [Matrix.adjugate_apply]
  apply matrix_det_norm_bound _ (by linarith)
  intro k l
  by_cases hkj : k = j
  · subst k
    by_cases hli : l = i
    · subst l
      simpa using hB
    · simpa [Pi.single_apply, hli] using (show (0 : ℝ) ≤ B by linarith)
  · simpa [Matrix.updateRow_apply, hkj] using hM k l

theorem matrix_inv_norm_bound {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {B : ℝ}
    (hB : 1 ≤ B) (hM : ∀ i j, ‖M i j‖ ≤ B) (i j : Fin m) :
    ‖M⁻¹ i j‖ ≤ ((m.factorial : ℝ) * B ^ m) / ‖M.det‖ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (matrix_adjugate_norm_bound M hB hM i j) (inv_nonneg.mpr (norm_nonneg M.det))

end ModifiedCartan
