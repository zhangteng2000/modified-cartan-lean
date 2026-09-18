import ModifiedCartan.PartitionTheorem

noncomputable section
set_option autoImplicit false
open Filter Topology Set Metric Finset
namespace ModifiedCartan

theorem cclass_univ_of_zeroSum {p : ℕ} {f : Family p} {U : Set ℂ}
    (hU : U ⊆ disk 1) (hs : ZeroSum f) (k : Fin p)
    (hb : ∀ j, LocallyBounded (fun n z => f j n z / f k n z) U) :
    IsCClass f univ U := by
  refine ⟨k, mem_univ k, fun j _ => hb j, ?_⟩
  have hzero : CompactConvergence (fun (_ : ℕ) (_ : ℂ) => (0 : ℂ)) (fun _ => 0) U :=
    fun K _ _ => (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)).tendstoUniformlyOn_const K
  apply compactConvergence_congr hzero
  intro n z hz
  simp only [← Finset.sum_div, hs n z (hU hz), zero_div]

theorem partitionProperty_zero (U : Set ℂ) : PartitionProperty 0 U := by
  intro f _ _
  refine ⟨id, strictMono_id, ⟨{ parts := ∅, cover := ?_, disjoint := ?_, classes := ?_ }⟩⟩
  · intro i; exact i.elim0
  · simp
  · simp

theorem partitionProperty_one (U : Set ℂ) : PartitionProperty 1 U := by
  intro f hf hs
  have hz : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have h := hs 0 0 hz
  simp only [Fin.sum_univ_one] at h
  exact ((hf 0 0).2 0 hz h).elim

theorem partitionProperty_two : PartitionProperty 2 (disk 1) := by
  intro f hf hs
  have hquot : ∀ n z, z ∈ disk 1 → f 1 n z / f 0 n z = -1 := by
    intro n z hz
    have h := hs n z hz
    rw [Fin.sum_univ_two] at h
    apply (div_eq_iff ((hf 0 n).2 z hz)).mpr
    linear_combination h
  have hb : ∀ j, LocallyBounded (fun n z => f j n z / f 0 n z) (disk 1) := by
    intro j
    fin_cases j
    · exact quotient_bounded_refl (fun n => (hf 0 n).2)
    · intro K hK _
      refine ⟨1, ?_⟩
      intro n z hz
      change ‖f 1 n z / f 0 n z‖ ≤ 1
      rw [hquot n z (hK hz)]
      norm_num
  have hc := cclass_univ_of_zeroSum (Subset.refl _) hs 0 hb
  refine ⟨id, strictMono_id, ⟨{ parts := {Finset.univ}, cover := ?_, disjoint := ?_, classes := ?_ }⟩⟩
  · intro i
    exact ⟨univ, mem_singleton_self _, mem_univ i⟩
  · intro I hI J hJ hne
    exact (hne ((mem_singleton.mp hI).trans (mem_singleton.mp hJ).symm)).elim
  · intro I hI
    have he : I = Finset.univ := mem_singleton.mp hI
    simpa only [he] using cclass_subsequence hc strictMono_id

/-- A positive partition radius exists for every finite family, including 0, 1, 2 terms. -/
theorem partition_exists_positive_radius (p : ℕ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ PartitionProperty p (disk r) := by
  by_cases hp : 3 ≤ p
  · obtain ⟨r, hr, hr1, hp⟩ := partitionTheorem_proved p hp
    exact ⟨r, hr, hr1.le, hp⟩
  · interval_cases p
    · exact ⟨1, by norm_num, le_rfl, partitionProperty_zero _⟩
    · exact ⟨1, by norm_num, le_rfl, partitionProperty_one _⟩
    · exact ⟨1, by norm_num, le_rfl, partitionProperty_two⟩

end ModifiedCartan
