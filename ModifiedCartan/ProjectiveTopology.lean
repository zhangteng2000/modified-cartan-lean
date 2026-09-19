import ModifiedCartan.ProjectiveCoordinates
import Mathlib.Topology.Constructions

noncomputable section
set_option autoImplicit false
open Set Topology
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

/-- The standard quotient topology of nonzero vectors by nonzero scalars. -/
instance projectivizationTopology (p : ℕ) : TopologicalSpace (ℙ ℂ (Fin p → ℂ)) := by
  unfold Projectivization
  infer_instance

instance projectiveXTopology (p : ℕ) : TopologicalSpace (ProjectiveX p) :=
  inferInstanceAs (TopologicalSpace {q : ℙ ℂ (Fin p → ℂ) | homogeneousZeroSum q.rep})

theorem projective_mk_isQuotientMap (p : ℕ) :
    IsQuotientMap (Projectivization.mk' ℂ :
      {x : Fin p → ℂ // x ≠ 0} → ℙ ℂ (Fin p → ℂ)) :=
  isQuotientMap_quotient_mk'

theorem projective_mk_coordinate_ne_zero {p : ℕ} (k : Fin p)
    {x : Fin p → ℂ} (hx : x ≠ 0) :
    (Projectivization.mk ℂ x hx).rep k ≠ 0 ↔ x k ≠ 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) x hx
  rw [← hc]
  change (c : ℂ) * x k ≠ 0 ↔ x k ≠ 0
  exact mul_ne_zero_iff.trans (and_iff_right c.ne_zero)

def projectiveChartSet {p : ℕ} (k : Fin p) : Set (ℙ ℂ (Fin p → ℂ)) :=
  {q | q.rep k ≠ 0}

theorem projectiveChartSet_isOpen {p : ℕ} (k : Fin p) :
    IsOpen (projectiveChartSet k) := by
  apply (projective_mk_isQuotientMap p).isCoinducing.isOpen_preimage.mp
  have heq : (Projectivization.mk' ℂ) ⁻¹' projectiveChartSet k =
      {x : {x : Fin p → ℂ // x ≠ 0} | x.val k ≠ 0} := by
    ext x
    exact projective_mk_coordinate_ne_zero k x.property
  rw [heq]
  exact isOpen_ne_fun ((continuous_apply k).comp continuous_subtype_val) continuous_const

theorem projectiveChart_normalize_continuous {p : ℕ} (k : Fin p) :
    Continuous (fun q : projectiveChartSet k => normalizeCoordinates k q.val.rep) := by
  let Q := Projectivization.mk' ℂ (V := Fin p → ℂ)
  have hQ := (projective_mk_isQuotientMap p).restrictPreimage_isOpen
    (projectiveChartSet_isOpen k)
  apply hQ.continuous_iff.mpr
  have heq : (fun q : Q ⁻¹' projectiveChartSet k =>
      normalizeCoordinates k (Q q.val).rep) =
      (fun q : Q ⁻¹' projectiveChartSet k => normalizeCoordinates k q.val.val) := by
    funext q
    exact normalizeCoordinates_projective_mk k q.val.property
  change Continuous (fun q : Q ⁻¹' projectiveChartSet k =>
    normalizeCoordinates k (Q q.val).rep)
  rw [heq]
  apply continuous_pi
  intro j
  apply ((continuous_apply j).comp
    (continuous_subtype_val.comp continuous_subtype_val)).div
      ((continuous_apply k).comp (continuous_subtype_val.comp continuous_subtype_val))
  intro q
  exact (projective_mk_coordinate_ne_zero k q.val.property).mp q.property

def projectiveAffineChartEquiv {p : ℕ} (k : Fin p) :
    projectiveChartSet k ≃ {x : Fin p → ℂ | x k = 1} where
  toFun q := ⟨normalizeCoordinates k q.val.rep, div_self q.property⟩
  invFun x := ⟨Projectivization.mk ℂ x.val
    (fun h => one_ne_zero (x.property.symm.trans (congrFun h k))),
    (projective_mk_coordinate_ne_zero k _).mpr (by rw [x.property]; exact one_ne_zero)⟩
  left_inv q := by
    apply Subtype.ext
    change Projectivization.mk ℂ (normalizeCoordinates k q.val.rep) _ = q.val
    rw [projective_mk_normalizeCoordinates k q.property q.val.rep_nonzero,
      Projectivization.mk_rep]
  right_inv x := by
    apply Subtype.ext
    change normalizeCoordinates k (Projectivization.mk ℂ x.val _).rep = x.val
    rw [normalizeCoordinates_projective_mk, normalizeCoordinates_fixed k x.property]

/-- An affine chart for the actual quotient-topological projective space. -/
def projectiveAffineChartHomeomorph {p : ℕ} (k : Fin p) :
    projectiveChartSet k ≃ₜ {x : Fin p → ℂ | x k = 1} where
  toEquiv := projectiveAffineChartEquiv k
  continuous_toFun := (projectiveChart_normalize_continuous k).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (projective_mk_isQuotientMap p).continuous.comp
      (continuous_subtype_val.subtype_mk _)

theorem projectiveX_normalize_continuous {p : ℕ} (k : Fin p) :
    Continuous (fun q : ProjectiveX p => normalizeCoordinates k q.val.rep) := by
  let f : ProjectiveX p → projectiveChartSet k := fun q => ⟨q.val, q.property.1 k⟩
  exact (projectiveChart_normalize_continuous k).comp
    (continuous_subtype_val.subtype_mk (fun q => q.property.1 k))

def projectiveXHomeomorphNormalized {p : ℕ} (k : Fin p) :
    ProjectiveX p ≃ₜ (normalizedHyperplaneEquations k).locus where
  toEquiv := projectiveXEquivNormalized k
  continuous_toFun := (projectiveX_normalize_continuous k).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (projective_mk_isQuotientMap p).continuous.comp
      (continuous_subtype_val.subtype_mk _)

end ModifiedCartan
