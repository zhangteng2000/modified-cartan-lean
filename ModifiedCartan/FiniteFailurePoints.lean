import ModifiedCartan.FailurePoints

noncomputable section
set_option autoImplicit false
open Filter Set
namespace ModifiedCartan

/-- One compact set and one nonnegative bound suffice for a finite family of
failure points, even when the ambient open set is disconnected. -/
theorem finite_unit_failure_points {ι : Type*} [Fintype ι]
    (A : ι → ℕ → ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hA : ∀ i n z, z ∈ U → A i n z ≠ 0)
    (hno : ∀ i, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence
      (fun n z => (A i (φ n) z)⁻¹) (fun _ => 0) U) :
    ∃ K : Set ℂ, K ⊆ U ∧ IsCompact K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ i, ∃ z ∈ K, Real.log ‖A i n z‖ ≤ C := by
  choose K hKU hK C hC hp using fun i => unit_failure_points hU (hA i) (hno i)
  refine ⟨⋃ i, K i, iUnion_subset hKU, isCompact_iUnion hK,
    ∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  filter_upwards [eventually_all.mpr hp] with n hn
  intro i
  obtain ⟨z, hz, hzi⟩ := hn i
  exact ⟨z, mem_iUnion.mpr ⟨i, hz⟩, hzi.trans
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))⟩

end ModifiedCartan
