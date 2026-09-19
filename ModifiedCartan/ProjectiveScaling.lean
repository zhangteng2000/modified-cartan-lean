import ModifiedCartan.ProjectiveCoordinates
import ModifiedCartan.PartitionTori

noncomputable section
set_option autoImplicit false
open Set Finset
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

theorem isAdmissiblePartition_smul {p : ℕ} {x : Fin p → ℂ} {c : ℂ}
    (hc : c ≠ 0) (P : IndexPartition p) :
    IsAdmissiblePartition (c • x) P ↔ IsAdmissiblePartition x P := by
  constructor
  · intro h I hI
    have hs := h I hI
    change ∑ j ∈ I, c * x j = 0 at hs
    rw [← Finset.mul_sum] at hs
    exact (mul_eq_zero.mp hs).resolve_left hc
  · intro h I hI
    change ∑ j ∈ I, c * x j = 0
    rw [← Finset.mul_sum, h I hI, mul_zero]

theorem isAdmissiblePartition_normalize {p : ℕ} (k : Fin p) {x : Fin p → ℂ}
    (hx : x k ≠ 0) (P : IndexPartition p) :
    IsAdmissiblePartition (normalizeCoordinates k x) P ↔ IsAdmissiblePartition x P := by
  have heq : normalizeCoordinates k x = (x k)⁻¹ • x := by
    funext j
    simp [normalizeCoordinates, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact isAdmissiblePartition_smul (inv_ne_zero hx) P

/-- Independent nonzero scalings on each part, considered as actual projective points. -/
def homogeneousPartitionTorus {p : ℕ} (x : Fin p → ℂ) (P : IndexPartition p) :
    Set (ℙ ℂ (Fin p → ℂ)) :=
  {q | ∃ s : P.parts → ℂ, (∀ I, s I ≠ 0) ∧
    ∃ h : partitionTorusParam x P s ≠ 0, Projectivization.mk ℂ (partitionTorusParam x P s) h = q}

theorem normalized_partition_projective_iff {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (P : IndexPartition p) (k : Fin p) (hxk : x k = 1)
    (q : ℙ ℂ (Fin p → ℂ)) (hq : q.rep k ≠ 0) :
    normalizeCoordinates k q.rep ∈ normalizedPartitionTorus x P k ↔
      q ∈ homogeneousPartitionTorus x P := by
  constructor
  · rintro ⟨s, hs, _, hparam⟩
    have hn : partitionTorusParam x P s ≠ 0 := by
      intro h
      exact mul_ne_zero (hs (indexPart P k)) (hx k) (congrFun h k)
    have hnormal : normalizeCoordinates k q.rep ≠ 0 := by
      rw [← hparam]
      exact hn
    refine ⟨s, hs, hn, ?_⟩
    calc
      Projectivization.mk ℂ (partitionTorusParam x P s) hn =
          Projectivization.mk ℂ (normalizeCoordinates k q.rep) hnormal := by congr 1
      _ = q := by
        rw [projective_mk_normalizeCoordinates k hq q.rep_nonzero, Projectivization.mk_rep]
  · rintro ⟨s, hs, hn, rfl⟩
    rw [normalizeCoordinates_projective_mk]
    refine ⟨fun I => s I / s (indexPart P k),
      fun I => div_ne_zero (hs I) (hs _), div_self (hs _), ?_⟩
    funext j
    simp only [partitionTorusParam, normalizeCoordinates, hxk, mul_one]
    ring

theorem homogeneousPartitionTorus_subset_projectiveX {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) {P : IndexPartition p} (hP : IsAdmissiblePartition x P) :
    homogeneousPartitionTorus x P ⊆ ProjectiveX p := by
  rintro q ⟨s, hs, hn, rfl⟩
  apply (homogeneousZeroSum_projective_mk hn).mpr
  refine ⟨fun j => mul_ne_zero (hs _) (hx j), ?_⟩
  have hr : RatesConstantOnParts P (fun j => s (indexPart P j)) := by
    intro I hI i hi j hj
    change s (indexPart P i) = s (indexPart P j)
    rw [indexPart_eq_of_mem P hI hi, indexPart_eq_of_mem P hI hj]
  have hm := moments_zero_of_exponentialSum_zero (exponentialSum_zero_of_admissible hP hr) 1
  simpa only [moment, pow_one, partitionTorusParam, mul_comm] using hm

end ModifiedCartan
