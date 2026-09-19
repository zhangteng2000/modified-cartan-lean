import ModifiedCartan.PartitionTori
import ModifiedCartan.AffineSliceManifold

noncomputable section
set_option autoImplicit false
open Set Finset Topology Manifold
open scoped Manifold ContDiff
namespace ModifiedCartan

theorem normalizedPartitionTorus_mem_affine_iff {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (P : IndexPartition p) (k : Fin p) (y : Fin p → ℂ) :
    y ∈ normalizedPartitionTorus x P k ↔
      (∀ j, y j ≠ 0) ∧ y - x ∈ partitionVelocitySubspace x P k := by
  rw [normalizedPartitionTorus_mem_iff hx, mem_partitionVelocitySubspace_iff hx]
  simp only [Pi.sub_apply, sub_eq_zero, RatesConstantOnParts, sub_div,
    div_self (hx _), sub_left_inj]

def partitionTorusOpen {p : ℕ} (x : Fin p → ℂ) (P : IndexPartition p) (k : Fin p) :
    TopologicalSpace.Opens (partitionVelocitySubspace x P k) where
  carrier := {v | ∀ j, x j + v.val j ≠ 0}
  is_open' := by
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne_fun (continuous_const.add
      ((continuous_apply j).comp continuous_subtype_val)) continuous_const

def partitionTorusModelMap {p : ℕ} (x : Fin p → ℂ) (P : IndexPartition p) (k : Fin p)
    (v : partitionTorusOpen x P k) : Fin p → ℂ := x + (v.val : Fin p → ℂ)

def partitionTorusModelBase {p : ℕ} {x : Fin p → ℂ} (hx : ∀ j, x j ≠ 0)
    (P : IndexPartition p) (k : Fin p) : partitionTorusOpen x P k :=
  ⟨0, by intro j; simpa using hx j⟩

theorem partitionTorusModelMap_mem {p : ℕ} {x : Fin p → ℂ} (hx : ∀ j, x j ≠ 0)
    (P : IndexPartition p) (k : Fin p) (v : partitionTorusOpen x P k) :
    partitionTorusModelMap x P k v ∈ normalizedPartitionTorus x P k := by
  apply (normalizedPartitionTorus_mem_affine_iff hx P k _).mpr
  exact ⟨v.property, by simpa [partitionTorusModelMap] using v.val.property⟩

theorem partitionTorusModelMap_range {p : ℕ} {x : Fin p → ℂ} (hx : ∀ j, x j ≠ 0)
    (P : IndexPartition p) (k : Fin p) :
    range (partitionTorusModelMap x P k) = normalizedPartitionTorus x P k := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact partitionTorusModelMap_mem hx P k v
  · intro hy
    obtain ⟨hyn, hv⟩ := (normalizedPartitionTorus_mem_affine_iff hx P k y).mp hy
    refine ⟨⟨⟨y - x, hv⟩, fun j => by simpa using hyn j⟩, ?_⟩
    change x + (y - x) = y
    abel

theorem partitionTorusModelMap_isImmersion {p : ℕ} (x : Fin p → ℂ)
    (P : IndexPartition p) (k : Fin p) :
    IsImmersion 𝓘(ℂ, partitionVelocitySubspace x P k) 𝓘(ℂ, Fin p → ℂ) 1
      (partitionTorusModelMap x P k) :=
  affine_open_slice_isImmersion _ _ _

theorem partitionTorusModelMap_isEmbedding {p : ℕ} (x : Fin p → ℂ)
    (P : IndexPartition p) (k : Fin p) :
    IsEmbedding (partitionTorusModelMap x P k) := affine_open_slice_isEmbedding _ _ _

end ModifiedCartan
