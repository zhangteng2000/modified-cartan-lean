import ModifiedCartan.NormalizedParts

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

def mergedFamily {p q : ℕ} (f : Family p) (assign : Fin p → Fin q) : Family q :=
  fun k n z => ∑ j ∈ assignmentPart assign k, f j n z

def liftedIndices {p q : ℕ} (assign : Fin p → Fin q) (I : Finset (Fin q)) : Finset (Fin p) :=
  univ.filter (fun j => assign j ∈ I)

theorem mem_liftedIndices {p q : ℕ} {assign : Fin p → Fin q} {I : Finset (Fin q)} {j : Fin p} :
    j ∈ liftedIndices assign I ↔ assign j ∈ I := by simp [liftedIndices]

theorem liftedIndices_sum {p q : ℕ} (assign : Fin p → Fin q) (I : Finset (Fin q)) (v : Fin p → ℂ) :
    ∑ j ∈ liftedIndices assign I, v j = ∑ k ∈ I, ∑ j ∈ assignmentPart assign k, v j := by
  classical
  simp only [liftedIndices, assignmentPart, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  convert! (sum_ite_eq I (assign j) (fun _ => v j)).symm using 1
  apply sum_congr rfl
  intro k hk
  split_ifs <;> rfl

theorem liftedIndices_disjoint {p q : ℕ} (assign : Fin p → Fin q) {I J : Finset (Fin q)}
    (h : Disjoint I J) : Disjoint (liftedIndices assign I) (liftedIndices assign J) := by
  apply disjoint_left.mpr
  intro j hi hj
  exact disjoint_left.mp h (mem_liftedIndices.mp hi) (mem_liftedIndices.mp hj)

theorem liftedIndices_univ {p q : ℕ} (assign : Fin p → Fin q) :
    liftedIndices assign univ = univ := by ext; simp [mem_liftedIndices]

theorem mergedFamily_zeroSum {p q : ℕ} {f : Family p} (hs : ZeroSum f)
    (assign : Fin p → Fin q) : ZeroSum (mergedFamily f assign) := by
  intro n z hz
  change (∑ k, ∑ j ∈ assignmentPart assign k, f j n z) = 0
  rw [assignmentPart_sum]
  exact hs n z hz

/-- C classes lift through a genuine merging of indices when the internal
ratios of each merged block are locally bounded in both required directions. -/
theorem cclass_unmerge {p q : ℕ} {f : Family p} (assign : Fin p → Fin q)
    (rep : Fin q → Fin p) (hrep : ∀ k, assign (rep k) = k) {U : Set ℂ}
    (hunit : ∀ k n z, z ∈ U → mergedFamily f assign k n z ≠ 0)
    (hforward : ∀ j, LocallyBounded
      (fun n z => f j n z / mergedFamily f assign (assign j) n z) U)
    (hback : ∀ k, LocallyBounded
      (fun n z => mergedFamily f assign k n z / f (rep k) n z) U)
    {I : Finset (Fin q)} (hI : IsCClass (mergedFamily f assign) I U) :
    IsCClass f (liftedIndices assign I) U := by
  obtain ⟨k, hk, hb, hsum⟩ := hI
  refine ⟨rep k, mem_liftedIndices.mpr (by simpa [hrep] using hk), ?_, ?_⟩
  · intro j hj
    have hjI := mem_liftedIndices.mp hj
    have h1 := quotient_bounded_trans (hunit (assign j)) (hforward j) (hb (assign j) hjI)
    exact quotient_bounded_trans (hunit k) h1 (hback k)
  · have hh := compactConvergence_zero_mul hsum (hback k)
    apply compactConvergence_congr hh
    intro n z hz
    simp only [← sum_div]
    rw [liftedIndices_sum assign I]
    change ((∑ x ∈ I, mergedFamily f assign x n z) / mergedFamily f assign k n z) *
      (mergedFamily f assign k n z / f (rep k) n z) =
      (∑ x ∈ I, mergedFamily f assign x n z) / f (rep k) n z
    field_simp [hunit k n z hz]

end ModifiedCartan
