import ModifiedCartan.AbsorptionLinearAlgebra

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

theorem eventually_not_of_no_strict_subsequence {P : ℕ → Prop}
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n)) : ∀ᶠ n in atTop, ¬ P n := by
  by_contra hn
  have hf : ∃ᶠ n in atTop, P n := by simpa only [Filter.Frequently,not_not] using hn
  exact hno (extraction_of_frequently_atTop hf)

theorem eventually_all_not_of_no_strict_subsequence {ι : Type*} [Finite ι]
    (P : ι → ℕ → Prop) (hno : ∀ i, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P i (φ n)) :
    ∀ᶠ n in atTop, ∀ i, ¬ P i n :=
  eventually_all.mpr (fun i => eventually_not_of_no_strict_subsequence (hno i))

theorem eventually_at_most_one_of_no_two_subsequences {ι : Type*} [Finite ι]
    (P : ι → ℕ → Prop)
    (hno : ∀ i j, i ≠ j → ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P i (φ n) ∧ P j (φ n)) :
    ∀ᶠ n in atTop, ∀ i j, P i n → P j n → i = j := by
  have he : ∀ i j, ∀ᶠ n in atTop, P i n → P j n → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ _ _ => hij)
    · exact (eventually_not_of_no_strict_subsequence (P := fun n => P i n ∧ P j n) (hno i j hij)).mono
        (fun _ hn hi hj => False.elim (hn ⟨hi,hj⟩))
  exact eventually_all.mpr (fun i => eventually_all.mpr (he i))

/-- A single finite label can be fixed after extraction so that every other
case fails at every selected index; initial exceptional indices are removed. -/
theorem subsequence_all_but_one_fail {ι : Type*} [Finite ι] [Nonempty ι]
    (P : ι → ℕ → Prop)
    (hunique : ∀ᶠ n in atTop, ∀ i j, P i n → P j n → i = j) :
    ∃ i : ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n j, j ≠ i → ¬ P j (φ n) := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp hunique
  have hex : ∀ n : ℕ, ∃ i : ι, ∀ j, j ≠ i → ¬ P j (N+n) := by
    intro n
    by_cases hh : ∃ i, P i (N+n)
    · obtain ⟨i,hi⟩ := hh
      exact ⟨i,fun j hji hj => hji (hN (N+n) (by omega) j i hj hi)⟩
    · exact ⟨Classical.choice inferInstance,fun j _ hj => hh ⟨j,hj⟩⟩
  choose a ha using hex
  obtain ⟨i,ψ,hψ,hfixed⟩ := finite_constant_subsequence a
  refine ⟨i,fun n => N+ψ n,fun x y hxy => Nat.add_lt_add_left (hψ hxy) N,?_⟩
  intro n j hji
  exact ha (ψ n) j (by simpa only [hfixed n] using hji)

end ModifiedCartan
