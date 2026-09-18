import ModifiedCartan.QuotientStabilization

noncomputable section
set_option autoImplicit false
open Finset
namespace ModifiedCartan

/-- A partition subordinate to representatives of the maximal preorder classes. -/
structure DominancePartition {p : ℕ} (R : FinitePreorder (Fin p)) where
  t : ℕ
  count : t = (maximalClasses R).card
  representative : Fin t → Fin p
  assign : Fin p → Fin t
  maximal : ∀ i, PreorderMaximal R (representative i)
  dominates : ∀ j, R.rel j (representative (assign j))
  fixed : ∀ i, assign (representative i) = i
  distinct : ∀ i j, i ≠ j → ¬ (R.rel (representative i) (representative j) ∧
    R.rel (representative j) (representative i))

theorem exists_dominancePartition {p : ℕ} (R : FinitePreorder (Fin p)) :
    Nonempty (DominancePartition R) := by
  classical
  let C := maximalClasses R
  let e : Fin C.card ≃ C := by simpa using (Fintype.equivFin C).symm
  have hc : ∀ i : Fin C.card, ∃ x, PreorderMaximal R x ∧ preorderClass R x = (e i).val :=
    fun i => mem_maximalClasses.mp (e i).property
  choose rep hmax hclass using hc
  have habove : ∀ j : Fin p, ∃ i : Fin C.card, R.rel j (rep i) := by
    intro j
    obtain ⟨y, hjy, hy⟩ := exists_preorderMaximal_above R j
    let i := e.symm ⟨preorderClass R y, mem_maximalClasses.mpr ⟨y, hy, rfl⟩⟩
    have heq : preorderClass R (rep i) = preorderClass R y := by simpa [i] using hclass i
    exact ⟨i, R.trans hjy ((preorderClass_eq_iff R _ _).mp heq).2⟩
  choose assign hbound using habove
  have hrep : ∀ i j, (R.rel (rep i) (rep j) ∧ R.rel (rep j) (rep i)) → i = j := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    rw [← hclass i, ← hclass j]
    exact (preorderClass_eq_iff R _ _).mpr hij
  refine ⟨⟨C.card, rfl, rep, assign, hmax, hbound, ?_, ?_⟩⟩
  · intro i
    apply hrep
    exact ⟨hmax i _ (hbound (rep i)), hbound (rep i)⟩
  · intro i j hne hij
    exact hne (hrep i j hij)

def assignmentPart {p t : ℕ} (assign : Fin p → Fin t) (i : Fin t) : Finset (Fin p) :=
  @Finset.filter _ (fun j => assign j = i) (Classical.decPred _) univ

theorem mem_assignmentPart {p t : ℕ} {assign : Fin p → Fin t} {i : Fin t} {j : Fin p} :
    j ∈ assignmentPart assign i ↔ assign j = i := by
  classical
  simp [assignmentPart]

theorem assignmentPart_disjoint {p t : ℕ} {assign : Fin p → Fin t} {i j : Fin t}
    (hij : i ≠ j) : Disjoint (assignmentPart assign i) (assignmentPart assign j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hi hj
  exact hij ((mem_assignmentPart.mp hi).symm.trans (mem_assignmentPart.mp hj))

theorem assignmentPart_sum {p t : ℕ} (assign : Fin p → Fin t) (f : Fin p → ℂ) :
    ∑ i, ∑ j ∈ assignmentPart assign i, f j = ∑ j, f j := by
  classical
  simp only [assignmentPart, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (assign j)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

/-- Actual C-classes on the fibers give the required set partition. -/
theorem cpartition_of_assignment {p t : ℕ} {f : Family p} {U : Set ℂ}
    (assign : Fin p → Fin t) (hc : ∀ i, IsCClass f (assignmentPart assign i) U) :
    Nonempty (CPartition f U) := by
  classical
  refine ⟨{ parts := univ.image (assignmentPart assign)
            cover := ?_
            disjoint := ?_
            classes := ?_ }⟩
  · intro j
    exact ⟨assignmentPart assign (assign j), mem_image.mpr ⟨assign j, mem_univ _, rfl⟩,
      mem_assignmentPart.mpr rfl⟩
  · intro I hI J hJ hne
    obtain ⟨i, _, rfl⟩ := mem_image.mp hI
    obtain ⟨j, _, rfl⟩ := mem_image.mp hJ
    exact assignmentPart_disjoint (fun hij => hne (congrArg _ hij))
  · intro I hI
    obtain ⟨i, _, rfl⟩ := mem_image.mp hI
    exact hc i

end ModifiedCartan
