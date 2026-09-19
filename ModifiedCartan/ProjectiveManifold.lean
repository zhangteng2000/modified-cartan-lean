import ModifiedCartan.ProjectiveTopology
import ModifiedCartan.NormalizedHyperplaneChart
import ModifiedCartan.AffineSliceManifold

noncomputable section
set_option autoImplicit false
open Set Finset Topology Manifold
open scoped LinearAlgebra.Projectivization Manifold ContDiff
namespace ModifiedCartan

theorem projectiveX_nonempty {p : ℕ} (hp : 2 ≤ p) : Nonempty (ProjectiveX p) := by
  classical
  let k : Fin p := ⟨0, by omega⟩
  let x : Fin p → ℂ := fun j => (if j = k then (p : ℂ) else 0) - 1
  have hx : ∀ j, x j ≠ 0 := by
    intro j
    by_cases hj : j = k
    · simp only [x, hj, if_pos, sub_ne_zero]
      exact_mod_cast (show p ≠ 1 by omega)
    · simp [x, hj]
  have hs : ∑ j, x j = 0 := by
    simp [x, Finset.sum_sub_distrib]
  have hx0 : x ≠ 0 := fun h => hx k (congrFun h k)
  exact ⟨⟨Projectivization.mk ℂ x hx0,
    (homogeneousZeroSum_projective_mk hx0).mpr ⟨hx, hs⟩⟩⟩

variable {p : ℕ} (k : Fin p) [Nonempty (ProjectiveX p)]

def projectiveXBasePoint : (normalizedHyperplaneEquations k).locus :=
  projectiveXEquivNormalized k (Classical.choice inferInstance)

def projectiveXHomeomorphOpen : ProjectiveX p ≃ₜ
    normalizedSliceOpen k (projectiveXBasePoint k).val :=
  (projectiveXHomeomorphNormalized k).trans
    (normalizedHyperplaneHomeomorphOpen k (projectiveXBasePoint k).property)

def projectiveXModelMap (q : ProjectiveX p) : normalizedDirectionSubspace k :=
  (projectiveXHomeomorphOpen k q).val

theorem projectiveXModelMap_isOpenEmbedding : IsOpenEmbedding (projectiveXModelMap k) :=
  (normalizedSliceOpen k (projectiveXBasePoint k).val).isOpen.isOpenEmbedding_subtypeVal.comp
    (projectiveXHomeomorphOpen k).isOpenEmbedding

/-- The standard affine complex chart on X_p, with a harmless translation of
the affine hyperplane to its linear direction space. -/
@[instance_reducible]
def projectiveXChartedSpace : ChartedSpace (normalizedDirectionSubspace k) (ProjectiveX p) :=
  (projectiveXModelMap_isOpenEmbedding k).singletonChartedSpace

theorem projectiveX_isManifold :
    letI := projectiveXChartedSpace k
    IsManifold 𝓘(ℂ, normalizedDirectionSubspace k) 1 (ProjectiveX p) :=
  (projectiveXModelMap_isOpenEmbedding k).isManifold_singleton

def projectiveXNormalize (q : ProjectiveX p) : Fin p → ℂ :=
  normalizeCoordinates k q.val.rep

theorem projectiveXNormalize_eq_affine (q : ProjectiveX p) :
    projectiveXNormalize k q = (projectiveXBasePoint k).val +
      (projectiveXModelMap k q : Fin p → ℂ) := by
  change normalizeCoordinates k q.val.rep = (projectiveXBasePoint k).val +
    (normalizeCoordinates k q.val.rep - (projectiveXBasePoint k).val)
  abel

theorem projectiveXNormalize_isImmersion :
    letI := projectiveXChartedSpace k
    IsImmersion 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ) 1
      (projectiveXNormalize k) := by
  letI := projectiveXChartedSpace k
  exact (affine_chart_isImmersion (normalizedDirectionSubspace k)
    (projectiveXBasePoint k).val (projectiveXModelMap_isOpenEmbedding k)).congr
      (funext fun q => (projectiveXNormalize_eq_affine k q).symm)

theorem projectiveXNormalize_isEmbedding : IsEmbedding (projectiveXNormalize k) :=
  IsEmbedding.subtypeVal.comp (projectiveXHomeomorphNormalized k).isEmbedding

theorem projectiveXNormalize_range :
    range (projectiveXNormalize k) = (normalizedHyperplaneEquations k).locus := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact normalizeCoordinates_mem k q.property
  · intro hx
    refine ⟨(projectiveXHomeomorphNormalized k).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((projectiveXHomeomorphNormalized k).apply_symm_apply ⟨x, hx⟩)

theorem projectiveX_metric_eq_normalized :
    letI := projectiveXChartedSpace k
    ∀ (x : ProjectiveX p) (v : TangentSpace 𝓘(ℂ, normalizedDirectionSubspace k) x),
      manifoldKobayashiRoyden x v =
        kobayashiRoyden (normalizedHyperplaneEquations k).locus (projectiveXNormalize k x)
          (mfderiv 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ)
            (projectiveXNormalize k) x v) := by
  letI := projectiveXChartedSpace k
  letI := projectiveX_isManifold k
  intro x v
  have h := manifold_metric_eq_coordinate_metric (projectiveXNormalize_isImmersion k)
    (projectiveXNormalize_isEmbedding k) x v
  rwa [projectiveXNormalize_range k] at h

theorem projectiveX_zero_finite_union :
    letI := projectiveXChartedSpace k
    ∀ (x : ProjectiveX p) (v : TangentSpace 𝓘(ℂ, normalizedDirectionSubspace k) x),
      manifoldKobayashiRoyden x v = 0 ↔
        mfderiv 𝓘(ℂ, normalizedDirectionSubspace k) 𝓘(ℂ, Fin p → ℂ)
          (projectiveXNormalize k) x v ∈
          ⋃ P ∈ admissiblePartitions (projectiveXNormalize k x),
            (partitionVelocitySubspace (projectiveXNormalize k x) P k : Set (Fin p → ℂ)) := by
  letI := projectiveXChartedSpace k
  letI := projectiveX_isManifold k
  intro x v
  rw [projectiveX_metric_eq_normalized k]
  exact Set.ext_iff.mp
    (normalizedHyperplane_zero_finite_union k (normalizeCoordinates_mem k x.property)) _

end ModifiedCartan
