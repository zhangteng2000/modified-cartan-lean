import ModifiedCartan.Convergence

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

/-- A strict diagonal subsequence eventually refines every member of a
nested sequence of strict subsequences. -/
theorem diagonal_subsequence_of_nested (s : ℕ → ℕ → ℕ) (hs : ∀ n, StrictMono (s n))
    (hnest : ∀ n, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ s (n+1) = s n ∘ ψ) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧ ∀ n, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      (fun k => δ (n+k)) = s n ∘ ψ := by
  classical
  have hrange : ∀ n m, n ≤ m → range (s m) ⊆ range (s n) := by
    intro n m hnm
    induction hnm with
    | refl => exact Subset.rfl
    | @step m hnm ih =>
      obtain ⟨ψ,_,hψ⟩ := hnest m
      rintro _ ⟨k,rfl⟩
      exact ih ⟨ψ k,(congrFun hψ k).symm⟩
  let δ : ℕ → ℕ := fun n => s n n
  have hδ : StrictMono δ := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨ψ,hψ,he⟩ := hnest n
    change s n n < s (n+1) (n+1)
    rw [he]
    exact (hs n (Nat.lt_succ_self n)).trans_le ((hs n).monotone (hψ.id_le (n+1)))
  refine ⟨δ,hδ,?_⟩
  intro n
  have hex : ∀ k : ℕ, ∃ l : ℕ, s n l = δ (n+k) := by
    intro k
    exact hrange n (n+k) (by omega) ⟨n+k,rfl⟩
  choose ψ hψ using hex
  refine ⟨ψ,?_,funext (fun k => (hψ k).symm)⟩
  intro i j hij
  apply (hs n).lt_iff_lt.mp
  rw [hψ i,hψ j]
  exact hδ (Nat.add_lt_add_left hij n)

/-- Countably many hereditary extraction requirements can be enforced on
tails of one actual strict subsequence. -/
theorem countable_subsequence_selection (P : ℕ → (ℕ → ℕ) → Prop)
    (hereditary : ∀ n (φ ψ : ℕ → ℕ), StrictMono φ → StrictMono ψ → P n φ → P n (φ ∘ ψ))
    (extract : ∀ n (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P n (φ ∘ ψ)) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧ ∀ n, ∃ N : ℕ, P n (fun k => δ (N+k)) := by
  classical
  let S := {φ : ℕ → ℕ // StrictMono φ}
  choose step hstep hP using (fun n (φ : S) => extract n φ φ.2)
  let s : ℕ → S := fun n => Nat.rec ⟨id,strictMono_id⟩
    (fun n φ => ⟨φ.1 ∘ step n φ,φ.2.comp (hstep n φ)⟩) n
  have hnest (n : ℕ) : (s (n+1)).1 = (s n).1 ∘ step n (s n) := rfl
  obtain ⟨δ,hδ,hrefine⟩ := diagonal_subsequence_of_nested (fun n => (s n).1)
    (fun n => (s n).2) (fun n => ⟨step n (s n),hstep n (s n),hnest n⟩)
  refine ⟨δ,hδ,?_⟩
  intro n
  obtain ⟨ψ,hψ,he⟩ := hrefine (n+1)
  refine ⟨n+1,?_⟩
  rw [he]
  exact hereditary n (s (n+1)).1 ψ (s (n+1)).2 hψ (hP n (s n))

end ModifiedCartan
