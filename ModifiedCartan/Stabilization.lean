import Mathlib.Tactic

/-! The integer counting step of Lemma 4.1. The analytic extraction and
maximal-preorder-class arguments are not asserted here. -/
namespace ModifiedCartan

theorem descending_count_bound {p : ℕ} {t : ℕ → ℕ}
    (hstrict : ∀ k, k + 1 < p → t (k + 1) < t k) :
    ∀ k, k < p → t k + k ≤ t 0 := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    intro hk
    have hi := ih (by omega)
    have hs := hstrict k hk
    omega

/-- p nonincreasing positive counts bounded initially by p must reach one
or have two adjacent equal counts. -/
theorem count_stabilization {p : ℕ} (hp : 1 ≤ p) (t : ℕ → ℕ)
    (hpos : ∀ k, k < p → 1 ≤ t k) (hbound : t 0 ≤ p)
    (hmono : ∀ k, k + 1 < p → t (k + 1) ≤ t k) :
    (∃ k, k < p ∧ t k = 1) ∨ (∃ k, k + 1 < p ∧ t k = t (k + 1)) := by
  by_contra hn
  push Not at hn
  have hstrict : ∀ k, k + 1 < p → t (k + 1) < t k := by
    intro k hk
    have hle := hmono k hk
    have hne := hn.2 k hk
    omega
  have hd := descending_count_bound hstrict (p - 1) (by omega)
  have hlo := hpos (p - 1) (by omega)
  have hne := hn.1 (p - 1) (by omega)
  omega

end ModifiedCartan
