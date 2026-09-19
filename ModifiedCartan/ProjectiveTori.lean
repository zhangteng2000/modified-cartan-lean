import ModifiedCartan.ProjectiveManifold
import ModifiedCartan.PartitionTorusManifold
import ModifiedCartan.AffineSliceDifferential
import ModifiedCartan.ProjectiveScaling

noncomputable section
set_option autoImplicit false
open Set Finset Topology Manifold Module
open scoped Manifold ContDiff
namespace ModifiedCartan

variable {p : ℕ} (k : Fin p) [Nonempty (ProjectiveX p)]

local instance : ChartedSpace (normalizedDirectionSubspace k) (ProjectiveX p) :=
  projectiveXChartedSpace k
local instance : IsManifold 𝓘(ℂ, normalizedDirectionSubspace k) 1 (ProjectiveX p) :=
  projectiveX_isManifold k

theorem projectiveXNormalize_mem (x : ProjectiveX p) :
    projectiveXNormalize k x ∈ (normalizedHyperplaneEquations k).locus :=
  normalizeCoordinates_mem k x.property

def projectivePartitionTorus (x : ProjectiveX p) (P : IndexPartition p) : Set (ProjectiveX p) :=
  projectiveXNormalize k ⁻¹' normalizedPartitionTorus (projectiveXNormalize k x) P k

theorem projectivePartitionTorus_eq_homogeneous (x : ProjectiveX p) (P : IndexPartition p) :
    projectivePartitionTorus k x P =
      Subtype.val ⁻¹' homogeneousPartitionTorus (projectiveXNormalize k x) P := by
  ext y
  exact normalized_partition_projective_iff (projectiveXNormalize_mem k x).1 P k
    ((mem_normalizedHyperplane k _).mp (projectiveXNormalize_mem k x)).2.2 y.val (y.property.1 k)

theorem projective_admissible_iff_rep (x : ProjectiveX p) (P : IndexPartition p) :
    IsAdmissiblePartition (projectiveXNormalize k x) P ↔ IsAdmissiblePartition x.val.rep P :=
  isAdmissiblePartition_normalize k (x.property.1 k) P

def projectiveTorusInclusion (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P)
    (v : partitionTorusOpen (projectiveXNormalize k x) P k) : ProjectiveX p :=
  (projectiveXHomeomorphNormalized k).symm
    ⟨partitionTorusModelMap (projectiveXNormalize k x) P k v,
      normalizedPartitionTorus_subset_hyperplane hP k (projectiveXNormalize_mem k x)
        (partitionTorusModelMap_mem (projectiveXNormalize_mem k x).1 P k v)⟩

theorem projectiveTorusInclusion_coordinates (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P)
    (v : partitionTorusOpen (projectiveXNormalize k x) P k) :
    projectiveXNormalize k (projectiveTorusInclusion k x P hP v) =
      partitionTorusModelMap (projectiveXNormalize k x) P k v :=
  congrArg Subtype.val ((projectiveXHomeomorphNormalized k).apply_symm_apply _)

theorem projectiveTorusInclusion_isEmbedding (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P) :
    IsEmbedding (projectiveTorusInclusion k x P hP) := by
  apply (projectiveXNormalize_isEmbedding k).of_comp_iff.mp
  have heq : projectiveXNormalize k ∘ projectiveTorusInclusion k x P hP =
      partitionTorusModelMap (projectiveXNormalize k x) P k :=
    funext (projectiveTorusInclusion_coordinates k x P hP)
  rw [heq]
  exact partitionTorusModelMap_isEmbedding _ _ _

theorem projectiveTorusInclusion_contMDiff (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P) :
    ContMDiff 𝓘(ℂ, partitionVelocitySubspace (projectiveXNormalize k x) P k)
      𝓘(ℂ, normalizedDirectionSubspace k) 1 (projectiveTorusInclusion k x P hP) := by
  apply (ContMDiff.iff_comp_isImmersion (projectiveXNormalize_isImmersion k)).mpr
  refine ⟨(projectiveTorusInclusion_isEmbedding k x P hP).continuous, ?_⟩
  have heq : projectiveXNormalize k ∘ projectiveTorusInclusion k x P hP =
      partitionTorusModelMap (projectiveXNormalize k x) P k :=
    funext (projectiveTorusInclusion_coordinates k x P hP)
  rw [heq]
  exact (partitionTorusModelMap_isImmersion _ _ _).contMDiff

theorem projectiveTorusInclusion_base (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P) :
    projectiveTorusInclusion k x P hP
      (partitionTorusModelBase (projectiveXNormalize_mem k x).1 P k) = x := by
  apply (projectiveXNormalize_isEmbedding k).injective
  rw [projectiveTorusInclusion_coordinates]
  simp [partitionTorusModelMap, partitionTorusModelBase]

theorem projectiveTorusInclusion_mfderiv_injective (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P)
    (y : partitionTorusOpen (projectiveXNormalize k x) P k) :
    Function.Injective (mfderiv 𝓘(ℂ, partitionVelocitySubspace (projectiveXNormalize k x) P k)
      𝓘(ℂ, normalizedDirectionSubspace k) (projectiveTorusInclusion k x P hP) y) := by
  have heq : projectiveXNormalize k ∘ projectiveTorusInclusion k x P hP =
      partitionTorusModelMap (projectiveXNormalize k x) P k :=
    funext (projectiveTorusInclusion_coordinates k x P hP)
  have H (u : TangentSpace 𝓘(ℂ, partitionVelocitySubspace (projectiveXNormalize k x) P k) y) :
      mfderiv 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ) (projectiveXNormalize k)
        (projectiveTorusInclusion k x P hP y)
        (mfderiv 𝓘(ℂ, partitionVelocitySubspace (projectiveXNormalize k x) P k)
          𝓘(ℂ, normalizedDirectionSubspace k) (projectiveTorusInclusion k x P hP) y u) =
        ((show partitionVelocitySubspace (projectiveXNormalize k x) P k from u) : Fin p → ℂ) := by
    have hc := mfderiv_comp_apply y
      ((projectiveXNormalize_isImmersion k).contMDiff.mdifferentiable (by norm_num)
        (projectiveTorusInclusion k x P hP y))
      ((projectiveTorusInclusion_contMDiff k x P hP).mdifferentiable (by norm_num) y) u
    erw [heq, affine_open_slice_mfderiv] at hc
    exact hc.symm
  intro u v huv
  have h := congrArg
    (mfderiv 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ)
      (projectiveXNormalize k) (projectiveTorusInclusion k x P hP y)) huv
  erw [H u, H v] at h
  exact Subtype.ext h

theorem projectiveTorusInclusion_range (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P) :
    range (projectiveTorusInclusion k x P hP) = projectivePartitionTorus k x P := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    change projectiveXNormalize k (projectiveTorusInclusion k x P hP v) ∈
      normalizedPartitionTorus (projectiveXNormalize k x) P k
    rw [projectiveTorusInclusion_coordinates]
    exact partitionTorusModelMap_mem (projectiveXNormalize_mem k x).1 P k v
  · intro hy
    change projectiveXNormalize k y ∈ normalizedPartitionTorus (projectiveXNormalize k x) P k at hy
    obtain ⟨v, hv⟩ := (partitionTorusModelMap_range
      (projectiveXNormalize_mem k x).1 P k).symm ▸ hy
    refine ⟨v, (projectiveXNormalize_isEmbedding k).injective ?_⟩
    exact (projectiveTorusInclusion_coordinates k x P hP v).trans hv

theorem projectiveTorusInclusion_mfderiv_coordinates (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P)
    (u : TangentSpace 𝓘(ℂ, partitionVelocitySubspace (projectiveXNormalize k x) P k)
      (partitionTorusModelBase (projectiveXNormalize_mem k x).1 P k)) :
    mfderiv 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ) (projectiveXNormalize k) x
      (mfderiv 𝓘(ℂ, partitionVelocitySubspace (projectiveXNormalize k x) P k)
        𝓘(ℂ, normalizedDirectionSubspace k) (projectiveTorusInclusion k x P hP)
          (partitionTorusModelBase (projectiveXNormalize_mem k x).1 P k) u) =
      ((show partitionVelocitySubspace (projectiveXNormalize k x) P k from u) : Fin p → ℂ) := by
  let b := partitionTorusModelBase (projectiveXNormalize_mem k x).1 P k
  have hc := mfderiv_comp_apply b
    ((projectiveXNormalize_isImmersion k).contMDiff.mdifferentiable (by norm_num)
      (projectiveTorusInclusion k x P hP b))
    ((projectiveTorusInclusion_contMDiff k x P hP).mdifferentiable (by norm_num) b) u
  have heq : projectiveXNormalize k ∘ projectiveTorusInclusion k x P hP =
      partitionTorusModelMap (projectiveXNormalize k x) P k :=
    funext (projectiveTorusInclusion_coordinates k x P hP)
  dsimp [b] at hc
  erw [projectiveTorusInclusion_base, heq,
    affine_open_slice_mfderiv] at hc
  exact hc.symm

/-- The image of the genuine manifold differential of the embedded torus at x. -/
def projectiveTorusTangentSpace (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P) :
    Submodule ℂ (TangentSpace 𝓘(ℂ, normalizedDirectionSubspace k) x) :=
  LinearMap.range (mfderiv 𝓘(ℂ, partitionVelocitySubspace (projectiveXNormalize k x) P k)
    𝓘(ℂ, normalizedDirectionSubspace k) (projectiveTorusInclusion k x P hP)
      (partitionTorusModelBase (projectiveXNormalize_mem k x).1 P k)).toLinearMap

theorem projectiveTorusTangentSpace_mem_iff (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P)
    (v : TangentSpace 𝓘(ℂ, normalizedDirectionSubspace k) x) :
    v ∈ projectiveTorusTangentSpace k x P hP ↔
      mfderiv 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ)
        (projectiveXNormalize k) x v ∈ partitionVelocitySubspace (projectiveXNormalize k x) P k := by
  unfold projectiveTorusTangentSpace
  constructor
  · rintro ⟨u, rfl⟩
    erw [projectiveTorusInclusion_mfderiv_coordinates]
    exact (show partitionVelocitySubspace (projectiveXNormalize k x) P k from u).property
  · intro hv
    let u : partitionVelocitySubspace (projectiveXNormalize k x) P k :=
      ⟨mfderiv 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ)
        (projectiveXNormalize k) x v, hv⟩
    refine ⟨u, ?_⟩
    apply immersion_mfderiv_injective ((projectiveXNormalize_isImmersion k).isImmersionAt x)
    erw [projectiveTorusInclusion_mfderiv_coordinates]

theorem projective_zero_directions (x : ProjectiveX p) :
    {v : TangentSpace 𝓘(ℂ, normalizedDirectionSubspace k) x | manifoldKobayashiRoyden x v = 0} =
      ⋃ (P : IndexPartition p) (hP : IsAdmissiblePartition (projectiveXNormalize k x) P),
        (projectiveTorusTangentSpace k x P hP : Set _) := by
  ext v
  change manifoldKobayashiRoyden x v = 0 ↔ _
  let w : Fin p → ℂ := mfderiv 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ)
    (projectiveXNormalize k) x v
  have hz : manifoldKobayashiRoyden x v = 0 ↔
      w ∈ ⋃ P ∈ admissiblePartitions (projectiveXNormalize k x),
        (partitionVelocitySubspace (projectiveXNormalize k x) P k : Set (Fin p → ℂ)) :=
    projectiveX_zero_finite_union k x v
  rw [hz]
  simp only [mem_iUnion, exists_prop, SetLike.mem_coe]
  constructor
  · rintro ⟨P, hP, hv⟩
    exact ⟨P, (mem_admissiblePartitions _ _).mp hP,
      (projectiveTorusTangentSpace_mem_iff k x P _ v).mpr hv⟩
  · rintro ⟨P, hP, hv⟩
    exact ⟨P, (mem_admissiblePartitions _ _).mpr hP,
      (projectiveTorusTangentSpace_mem_iff k x P hP v).mp hv⟩

theorem projectiveTorusTangentSpace_finrank_le (x : ProjectiveX p) (P : IndexPartition p)
    (hP : IsAdmissiblePartition (projectiveXNormalize k x) P) :
    finrank ℂ (projectiveTorusTangentSpace k x P hP) ≤ p / 2 - 1 := by
  unfold projectiveTorusTangentSpace
  let D : partitionVelocitySubspace (projectiveXNormalize k x) P k →ₗ[ℂ]
      TangentSpace 𝓘(ℂ, normalizedDirectionSubspace k) x :=
    (mfderiv 𝓘(ℂ, partitionVelocitySubspace (projectiveXNormalize k x) P k)
      𝓘(ℂ, normalizedDirectionSubspace k) (projectiveTorusInclusion k x P hP)
        (partitionTorusModelBase (projectiveXNormalize_mem k x).1 P k)).toLinearMap
  change finrank ℂ (LinearMap.range D) ≤ _
  exact (LinearMap.finrank_range_le D).trans
    (partitionVelocitySubspace_finrank_le (projectiveXNormalize_mem k x).1 hP k)

end ModifiedCartan
