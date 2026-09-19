import ModifiedCartan.CartanPairIndex

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

theorem pairAssignment_restore {p : ℕ} (a b : Fin (p+1)) (hab : a ≠ b) (j : Fin (p+1)) :
    a.succAbove (pairAssignment a b hab j) = if j = a then b else j := by
  classical
  unfold pairAssignment
  split_ifs <;> exact restore_eraseFinIndex _ _ _

theorem mergedFamily_assigned_pair {p : ℕ} (f : Family (p+1)) (a b : Fin (p+1)) (hab : a ≠ b)
    (j : Fin (p+1)) (n : ℕ) (z : ℂ) :
    mergedFamily f (pairAssignment a b hab) (pairAssignment a b hab j) n z =
      if j = a ∨ j = b then f a n z + f b n z else f j n z := by
  classical
  rw [mergedFamily_pair, pairAssignment_restore]
  by_cases hja : j = a
  · simp [hja]
  · by_cases hjb : j = b <;> simp [hja, hjb]

theorem mergedFamily_pair_unit {p : ℕ} {f : Family (p+1)} {U : Set ℂ}
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U) (a b : Fin (p+1)) (hab : a ≠ b)
    (hs : ∀ n, IsHolomorphicUnit (fun z => f a n z + f b n z) U) :
    ∀ k n, IsHolomorphicUnit (mergedFamily f (pairAssignment a b hab) k n) U := by
  intro k n
  by_cases hk : a.succAbove k = b
  · simpa only [show mergedFamily f (pairAssignment a b hab) k n =
        (fun z => f a n z + f b n z) by funext z; simp [mergedFamily_pair, hk]] using hs n
  · simpa only [show mergedFamily f (pairAssignment a b hab) k n =
        f (a.succAbove k) n by funext z; simp [mergedFamily_pair, hk]] using hf (a.succAbove k) n

/-- Exact recovery of original classes after merging any chosen pair. -/
theorem cclass_unmerge_pair {p : ℕ} {f : Family (p+1)} {U : Set ℂ}
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U) (a b : Fin (p+1)) (hab : a ≠ b)
    (hs : ∀ n, IsHolomorphicUnit (fun z => f a n z + f b n z) U)
    (hleft : LocallyBounded (fun n z => f a n z / (f a n z + f b n z)) U)
    (hright : LocallyBounded (fun n z => f b n z / (f a n z + f b n z)) U)
    (hback : LocallyBounded (fun n z => (f a n z + f b n z) / f b n z) U)
    {I : Finset (Fin p)} (hI : IsCClass (mergedFamily f (pairAssignment a b hab)) I U) :
    IsCClass f (liftedIndices (pairAssignment a b hab) I) U := by
  apply cclass_unmerge (pairAssignment a b hab) a.succAbove (pairAssignment_rep a b hab)
    (fun k n => (mergedFamily_pair_unit hf a b hab hs k n).2) _ _ hI
  · intro j
    by_cases hja : j = a
    · subst j
      apply locallyBounded_congr hleft
      intro n z _
      simp [mergedFamily_assigned_pair]
    · by_cases hjb : j = b
      · subst j
        apply locallyBounded_congr hright
        intro n z _
        simp [mergedFamily_assigned_pair]
      · apply locallyBounded_congr (quotient_bounded_refl (fun n => (hf j n).2))
        intro n z _
        simp [mergedFamily_assigned_pair, hja, hjb]
  · intro k
    by_cases hk : a.succAbove k = b
    · apply locallyBounded_congr hback
      intro n z _
      simp [mergedFamily_pair, hk]
    · apply locallyBounded_congr (quotient_bounded_refl (fun n => (hf (a.succAbove k) n).2))
      intro n z _
      simp [mergedFamily_pair, hk]

end ModifiedCartan
