import ModifiedCartan.TwoClassAbsorption

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

/-- Classical extraction on the full unit disk. The instances for three, four,
and five functions are proved in CartanThree, CartanFour, and CartanFive. -/
def CartanExtractionAt (p : ℕ) : Prop :=
  ∀ f : Family p, UnitFamily f → ZeroSum f →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (IsCClass (subsequence f φ) univ (disk 1) ∨
       ∃ I J : Finset (Fin p), Disjoint I J ∧
         IsCClass (subsequence f φ) I (disk 1) ∧ IsCClass (subsequence f φ) J (disk 1))

theorem five_two_classes_complement {f : Family 5} (hf : UnitFamily f)
    {I J : Finset (Fin 5)} (hd : Disjoint I J)
    (hI : IsCClass f I (disk 1)) (hJ : IsCClass f J (disk 1)) :
    I ∪ J = univ ∨ ∃ l : Fin 5, l ∉ I ∪ J ∧ insert l (I ∪ J) = univ := by
  have hne : (disk 1).Nonempty := ⟨0, by simp [disk]⟩
  have hi := cclass_card_ge_two hne (fun i n => (hf i n).2) hI
  have hj := cclass_card_ge_two hne (fun i n => (hf i n).2) hJ
  have hcard : 4 ≤ (I ∪ J).card := by rw [card_union_of_disjoint hd]; omega
  by_cases hfull : I ∪ J = univ
  · exact Or.inl hfull
  · right
    have hc : (I ∪ J).card = 4 := by
      have hlt := card_lt_card (ssubset_univ_iff.mpr hfull)
      have hupper : (I ∪ J).card ≤ 5 := (card_le_univ _).trans_eq (by simp)
      have hu : (univ : Finset (Fin 5)).card = 5 := by simp
      omega
    have hcomp : ((I ∪ J)ᶜ).card = 1 := by
      rw [card_compl, hc]
      simp
    obtain ⟨l, hl⟩ := card_eq_one.mp hcomp
    have hlmem : l ∈ (I ∪ J)ᶜ := hl.symm ▸ mem_singleton_self l
    refine ⟨l, Finset.mem_compl.mp hlmem, ?_⟩
    ext j
    constructor
    · intro _; exact mem_univ j
    · intro hj
      by_cases hjU : j ∈ I ∪ J
      · exact mem_insert_of_mem hjU
      · have hjs : j ∈ (I ∪ J)ᶜ := Finset.mem_compl.mpr hjU
        rw [hl] at hjs
        exact mem_insert.mpr (Or.inl (mem_singleton.mp hjs))

/-- Assemble the sharp-domain partition from the classical alternative.
SharpFive applies this to the proved five-function extraction. -/
theorem five_partition_from_cartan_alternative {f : Family 5}
    (hf : UnitFamily f) (hs : ZeroSum f)
    (halt : IsCClass f univ (disk 1) ∨ ∃ I J : Finset (Fin 5),
      Disjoint I J ∧ IsCClass f I (disk 1) ∧ IsCClass f J (disk 1))
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ disk 1)
    (hdiam : HasHyperbolicDiameterLE U (Real.log 3)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Nonempty (CPartition (subsequence f φ) U) := by
  rcases halt with hfull | ⟨I, J, hd, hI, hJ⟩
  · exact ⟨id, strictMono_id, cpartition_single_class (cclass_mono (cclass_subsequence hfull strictMono_id) hsub)⟩
  · rcases five_two_classes_complement hf hd hI hJ with hcover | ⟨l, hl, hcover⟩
    · exact ⟨id, strictMono_id, cpartition_two_classes
        (cclass_mono (cclass_subsequence hI strictMono_id) hsub)
        (cclass_mono (cclass_subsequence hJ strictMono_id) hsub) hd hcover⟩
    · exact cpartition_two_classes_one_remaining hf hs hI hJ hd hl hcover hU hsub hdiam

end ModifiedCartan
