import ModifiedCartan.AbsorptionLinearAlgebra

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

theorem isDominant_of_compact_cover {p : ℕ} {f : Family p} {I : Finset (Fin p)} {k : Fin p}
    {V : ℕ → Set ℂ} {U : Set ℂ}
    (hcover : ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∃ n, K ⊆ V n)
    (hdom : ∀ n, IsDominant f I (V n) k) : IsDominant f I U k := by
  refine ⟨(hdom 0).1,?_,?_⟩
  · intro j hj K hK hcK
    obtain ⟨n,hn⟩ := hcover K hK hcK
    exact (hdom n).2.1 j hj K hn hcK
  · intro K hK hcK
    obtain ⟨n,hn⟩ := hcover K hK hcK
    exact (hdom n).2.2 K hn hcK

/-- Finite class patterns and dominant indices can be fixed along an
exhaustion; the resulting statement concerns every compact subset of U. -/
theorem cartan_alternative_of_exhaustion {p : ℕ} {f : Family p} {V : ℕ → Set ℂ} {U : Set ℂ}
    (hcover : ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∃ N, ∀ n, N ≤ n → K ⊆ V n)
    (hlocal : ∀ n, IsCClass f Finset.univ (V n) ∨ ∃ I J : Finset (Fin p), Disjoint I J ∧
      IsCClass f I (V n) ∧ IsCClass f J (V n)) :
    IsCClass f Finset.univ U ∨ ∃ I J : Finset (Fin p), Disjoint I J ∧
      IsCClass f I U ∧ IsCClass f J U := by
  classical
  let Λ := Fin p ⊕ ((Finset (Fin p) × Fin p) × (Finset (Fin p) × Fin p))
  let P : Λ → Set ℂ → Prop := fun a W => match a with
    | Sum.inl k => IsDominant f Finset.univ W k
    | Sum.inr ((I,k),(J,l)) => Disjoint I J ∧ IsDominant f I W k ∧ IsDominant f J W l
  have hex : ∀ n, ∃ a : Λ, P a (V n) := by
    intro n
    rcases hlocal n with ⟨k,hk⟩ | ⟨I,J,hd,⟨k,hk⟩,⟨l,hl⟩⟩
    · exact ⟨Sum.inl k,hk⟩
    · exact ⟨Sum.inr ((I,k),(J,l)),hd,hk,hl⟩
  choose a ha using hex
  obtain ⟨a₀,φ,hφ,hfixed⟩ := finite_constant_subsequence a
  have hP : ∀ n, P a₀ (V (φ n)) := by
    intro n
    have hh := ha (φ n)
    rwa [hfixed n] at hh
  have hcover' : ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∃ n, K ⊆ V (φ n) := by
    intro K hK hcK
    obtain ⟨N,hN⟩ := hcover K hK hcK
    exact ⟨N,hN (φ N) (hφ.id_le N)⟩
  rcases a₀ with k | ⟨⟨I,k⟩,⟨J,l⟩⟩
  · exact Or.inl ⟨k,isDominant_of_compact_cover hcover' hP⟩
  · exact Or.inr ⟨I,J,(hP 0).1,⟨k,isDominant_of_compact_cover hcover' (fun n => (hP n).2.1)⟩,
      ⟨l,isDominant_of_compact_cover hcover' (fun n => (hP n).2.2)⟩⟩

end ModifiedCartan
