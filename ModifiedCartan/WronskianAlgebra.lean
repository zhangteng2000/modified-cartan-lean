import ModifiedCartan.Wronskian

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

/-- The Schur-complement determinant identity in the exact indexing used by the
Wronskian induction. It is proved by a column operation and Laplace expansion. -/
theorem determinant_last_column_residual {m : ℕ}
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (d : Fin m → ℂ)
    (hd : ∀ i : Fin m, ∑ j : Fin m, M i.castSucc j.castSucc * d j = M i.castSucc (Fin.last m)) :
    M.det = (M (Fin.last m) (Fin.last m) - ∑ j : Fin m, M (Fin.last m) j.castSucc * d j) *
      (M.submatrix Fin.castSucc Fin.castSucc).det := by
  classical
  let c : Fin (m + 1) → ℂ := Fin.snoc (fun j => -d j) 1
  let v : Fin (m + 1) → ℂ := fun i => ∑ j, c j * M i j
  let A := M.updateCol (Fin.last m) v
  have hdet : A.det = M.det := by
    simpa only [A, v, smul_eq_mul, c, Fin.snoc_last, one_mul] using
      Matrix.det_updateCol_sum M (Fin.last m) c
  have hv : ∀ i, v i = M i (Fin.last m) - ∑ j : Fin m, M i j.castSucc * d j := by
    intro i
    simp [v, c, Fin.sum_univ_castSucc, Finset.sum_neg_distrib, mul_comm, sub_eq_add_neg, add_comm]
  have hzero : ∀ i : Fin m, A i.castSucc (Fin.last m) = 0 := by
    intro i
    simp [A, hv, hd i]
  have hsub : A.submatrix Fin.castSucc Fin.castSucc = M.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp [A, Matrix.submatrix_apply, Fin.castSucc_ne_last]
  rw [← hdet, Matrix.det_succ_column A (Fin.last m), Fin.sum_univ_castSucc]
  have hsum : (∑ i : Fin m, (-1 : ℂ) ^ ((i.castSucc : Fin (m + 1)) + Fin.last m : ℕ) *
      A i.castSucc (Fin.last m) * (A.submatrix i.castSucc.succAbove (Fin.last m).succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hzero i, mul_zero, zero_mul]
  rw [hsum, zero_add, Fin.succAbove_last, hsub]
  simp only [Fin.val_last, pow_add, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  congr 1
  simp [A, hv]

theorem wronskian_last_column_residual {m : ℕ}
    (g : Fin (m + 1) → ℂ → ℂ) (z : ℂ) (d : Fin m → ℂ)
    (hd : ∀ i : Fin m, ∑ j : Fin m, iteratedDeriv (i : ℕ) (g j.castSucc) z * d j =
      iteratedDeriv (i : ℕ) (g (Fin.last m)) z) :
    wronskian g z = (iteratedDeriv m (g (Fin.last m)) z -
      ∑ j : Fin m, iteratedDeriv m (g j.castSucc) z * d j) *
      wronskian (fun j : Fin m => g j.castSucc) z := by
  exact determinant_last_column_residual (.of fun i j => iteratedDeriv (i : ℕ) (g j) z) d hd

end ModifiedCartan
