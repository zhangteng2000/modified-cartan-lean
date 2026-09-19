import ModifiedCartan.CartanPairs

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

theorem ratio_neg_one_symmetric {p : ℕ} {f : Family p} {U : Set ℂ}
    (hU : IsOpen U) {i j : Fin p}
    (h : CompactConvergence (fun n z => f i n z / f j n z) (fun _ => -1) U) :
    CompactConvergence (fun n z => f j n z / f i n z) (fun _ => -1) U := by
  simpa only [inv_div, inv_neg, inv_one] using compactConvergence_inv hU h continuousOn_const
    (fun _ _ => neg_ne_zero.mpr one_ne_zero)

/-- Distinct cancelling pairs either are disjoint or give a plus-one quotient.
This is the overlap step in the first Cartan normality branch. -/
theorem cancelling_pairs_disjoint_or_ratio_one {p : ℕ} {f : Family p} {U : Set ℂ}
    (hU : IsOpen U) (hf : ∀ i n, IsHolomorphicUnit (f i n) U)
    {a b c d : Fin p} (_hab : a ≠ b) (hcd : c ≠ d)
    (hne : ({a, b} : Finset (Fin p)) ≠ {c, d})
    (h1 : CompactConvergence (fun n z => f a n z / f b n z) (fun _ => -1) U)
    (h2 : CompactConvergence (fun n z => f c n z / f d n z) (fun _ => -1) U) :
    Disjoint ({a, b} : Finset (Fin p)) {c, d} ∨
      ∃ i j : Fin p, i ≠ j ∧
        CompactConvergence (fun n z => f i n z / f j n z) (fun _ => 1) U := by
  classical
  by_cases hd : Disjoint ({a, b} : Finset (Fin p)) {c, d}
  · exact Or.inl hd
  right
  obtain ⟨x, hx1, hx2⟩ := not_disjoint_iff.mp hd
  simp only [mem_insert, mem_singleton] at hx1 hx2
  rcases hx1 with hx1 | hx1 <;> rcases hx2 with hx2 | hx2
  · have hac : a = c := hx1.symm.trans hx2
    clear hx1 hx2
    subst c
    have hbd : b ≠ d := by intro he; subst d; exact hne rfl
    exact ⟨b, d, hbd, ratio_one_of_overlapping_cancellations hU hf (ratio_neg_one_symmetric hU h1) h2⟩
  · have had : a = d := hx1.symm.trans hx2
    clear hx1 hx2
    subst d
    have hbc : b ≠ c := by
      intro he
      subst c
      exact hne (by ext i; simp [or_comm])
    exact ⟨b, c, hbc, ratio_one_of_overlapping_cancellations hU hf
      (ratio_neg_one_symmetric hU h1) (ratio_neg_one_symmetric hU h2)⟩
  · have hbc : b = c := hx1.symm.trans hx2
    clear hx1 hx2
    subst c
    have had : a ≠ d := by
      intro he
      subst d
      exact hne (by ext i; simp [or_comm])
    exact ⟨a, d, had, ratio_one_of_overlapping_cancellations hU hf h1 h2⟩
  · have hbd : b = d := hx1.symm.trans hx2
    clear hx1 hx2
    subst d
    have hac : a ≠ c := by intro he; subst c; exact hne rfl
    exact ⟨a, c, hac, ratio_one_of_overlapping_cancellations hU hf h1 (ratio_neg_one_symmetric hU h2)⟩

end ModifiedCartan
