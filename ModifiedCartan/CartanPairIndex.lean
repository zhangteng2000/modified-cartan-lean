import ModifiedCartan.CartanUnmerge

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

def eraseFinIndex {p : ℕ} (a j : Fin (p+1)) (hj : j ≠ a) : Fin p :=
  Classical.choose (Fin.exists_succAbove_eq hj)

theorem restore_eraseFinIndex {p : ℕ} (a j : Fin (p+1)) (hj : j ≠ a) :
    a.succAbove (eraseFinIndex a j hj) = j := Classical.choose_spec (Fin.exists_succAbove_eq hj)

theorem eraseFinIndex_eq_iff {p : ℕ} (a j : Fin (p+1)) (hj : j ≠ a) (k : Fin p) :
    eraseFinIndex a j hj = k ↔ j = a.succAbove k := by
  constructor
  · intro he
    rw [← restore_eraseFinIndex a j hj, he]
  · intro he
    apply Fin.succAbove_right_injective
    rw [restore_eraseFinIndex, he]

def pairAssignment {p : ℕ} (a b : Fin (p+1)) (hab : a ≠ b) (j : Fin (p+1)) : Fin p := by
  classical
  exact if hj : j = a then eraseFinIndex a b hab.symm else eraseFinIndex a j hj

theorem pairAssignment_eq_iff {p : ℕ} (a b : Fin (p+1)) (hab : a ≠ b) (j : Fin (p+1)) (k : Fin p) :
    pairAssignment a b hab j = k ↔ j = a.succAbove k ∨ (j = a ∧ a.succAbove k = b) := by
  classical
  unfold pairAssignment
  split_ifs with hj
  · subst j
    rw [eraseFinIndex_eq_iff]
    simp [Fin.ne_succAbove, eq_comm]
  · rw [eraseFinIndex_eq_iff]
    simp [hj]

theorem pairAssignment_rep {p : ℕ} (a b : Fin (p+1)) (hab : a ≠ b) (k : Fin p) :
    pairAssignment a b hab (a.succAbove k) = k :=
  (pairAssignment_eq_iff a b hab _ _).mpr (Or.inl rfl)

theorem pairAssignment_fiber {p : ℕ} (a b : Fin (p+1)) (hab : a ≠ b) (k : Fin p) :
    assignmentPart (pairAssignment a b hab) k =
      if a.succAbove k = b then {a,b} else {a.succAbove k} := by
  classical
  ext j
  by_cases hk : a.succAbove k = b
  · simp [mem_assignmentPart, pairAssignment_eq_iff, hk, or_comm]
  · simp [mem_assignmentPart, pairAssignment_eq_iff, hk]

theorem mergedFamily_pair {p : ℕ} (f : Family (p+1)) (a b : Fin (p+1)) (hab : a ≠ b)
    (k : Fin p) (n : ℕ) (z : ℂ) :
    mergedFamily f (pairAssignment a b hab) k n z =
      if a.succAbove k = b then f a n z + f b n z else f (a.succAbove k) n z := by
  classical
  unfold mergedFamily
  rw [pairAssignment_fiber]
  split_ifs <;> simp [hab]

end ModifiedCartan
