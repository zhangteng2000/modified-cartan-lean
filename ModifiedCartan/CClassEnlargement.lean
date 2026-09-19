import ModifiedCartan.Convergence

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

theorem dominant_insert_negligible {p : ℕ} {f : Family p} {U : Set ℂ}
    {I : Finset (Fin p)} {k l : Fin p} (hk : IsDominant f I U k) (hl : l ∉ I)
    (hc : ∀ n, ContinuousOn (fun z => f l n z / f k n z) U)
    (hsmall : CompactConvergence (fun n z => f l n z / f k n z) (fun _ => 0) U) :
    IsDominant f (insert l I) U k := by
  refine ⟨mem_insert_of_mem hk.1, ?_, ?_⟩
  · intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact compactConvergence_locallyBounded hsmall hc
    · exact hk.2.1 j hj
  · intro K hKU hK
    have hh := (hsmall K hKU hK).add (hk.2.2 K hKU hK)
    simpa only [sum_insert hl, Pi.add_def, add_zero] using hh

theorem cpartition_single_class {p : ℕ} {f : Family p} {U : Set ℂ}
    (h : IsCClass f Finset.univ U) : Nonempty (CPartition f U) := by
  refine ⟨{ parts := {Finset.univ}
            cover := fun j => ⟨Finset.univ, mem_singleton_self _, Finset.mem_univ j⟩
            disjoint := ?_
            classes := ?_ }⟩
  · intro I hI J hJ hne
    exact (hne ((mem_singleton.mp hI).trans (mem_singleton.mp hJ).symm)).elim
  · intro I hI
    exact mem_singleton.mp hI ▸ h

theorem cpartition_two_classes {p : ℕ} {f : Family p} {U : Set ℂ}
    {I J : Finset (Fin p)} (hI : IsCClass f I U) (hJ : IsCClass f J U)
    (hd : Disjoint I J) (hcover : I ∪ J = Finset.univ) : Nonempty (CPartition f U) := by
  refine ⟨{ parts := {I, J}, cover := ?_, disjoint := ?_, classes := ?_ }⟩
  · intro j
    have hj : j ∈ I ∪ J := hcover.symm ▸ Finset.mem_univ j
    rcases mem_union.mp hj with hj | hj
    · exact ⟨I, by simp, hj⟩
    · exact ⟨J, by simp, hj⟩
  · intro A hA B hB hne
    simp only [mem_insert, mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hne rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hne rfl).elim
  · intro A hA
    simp only [mem_insert, mem_singleton] at hA
    rcases hA with rfl | rfl
    · exact hI
    · exact hJ

end ModifiedCartan
