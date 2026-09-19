import ModifiedCartan.NormalizedHyperplane
import Mathlib.LinearAlgebra.Projectivization.Basic

noncomputable section
set_option autoImplicit false
open Set Finset
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

def homogeneousZeroSum {p : ℕ} (x : Fin p → ℂ) : Prop :=
  (∀ j, x j ≠ 0) ∧ ∑ j, x j = 0

def ProjectiveX (p : ℕ) := {q : ℙ ℂ (Fin p → ℂ) | homogeneousZeroSum q.rep}

def normalizeCoordinates {p : ℕ} (k : Fin p) (x : Fin p → ℂ) : Fin p → ℂ :=
  fun j => x j / x k

theorem homogeneousZeroSum_smul {p : ℕ} {x : Fin p → ℂ} {c : ℂ}
    (hc : c ≠ 0) : homogeneousZeroSum (c • x) ↔ homogeneousZeroSum x := by
  simp only [homogeneousZeroSum, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    mul_eq_zero, mul_ne_zero_iff]
  constructor
  · rintro ⟨hn, hs⟩
    exact ⟨fun j => (hn j).2, hs.resolve_left hc⟩
  · rintro ⟨hn, hs⟩
    exact ⟨fun j => ⟨hc, hn j⟩, Or.inr hs⟩

theorem homogeneousZeroSum_projective_mk {p : ℕ} {x : Fin p → ℂ} (hx : x ≠ 0) :
    homogeneousZeroSum (Projectivization.mk ℂ x hx).rep ↔ homogeneousZeroSum x := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) x hx
  rw [← hc]
  exact homogeneousZeroSum_smul c.ne_zero

theorem normalizeCoordinates_smul {p : ℕ} (k : Fin p) (x : Fin p → ℂ)
    {c : ℂ} (hc : c ≠ 0) : normalizeCoordinates k (c • x) = normalizeCoordinates k x := by
  funext j
  exact mul_div_mul_left (x j) (x k) hc

theorem normalizeCoordinates_projective_mk {p : ℕ} (k : Fin p) {x : Fin p → ℂ}
    (hx : x ≠ 0) : normalizeCoordinates k (Projectivization.mk ℂ x hx).rep =
      normalizeCoordinates k x := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) x hx
  rw [← hc]
  exact normalizeCoordinates_smul k x c.ne_zero

theorem normalizeCoordinates_mem {p : ℕ} (k : Fin p) {x : Fin p → ℂ}
    (hx : homogeneousZeroSum x) :
    normalizeCoordinates k x ∈ (normalizedHyperplaneEquations k).locus := by
  apply (mem_normalizedHyperplane k _).mpr
  refine ⟨fun j => div_ne_zero (hx.1 j) (hx.1 k), ?_, div_self (hx.1 k)⟩
  change ∑ j, x j / x k = 0
  rw [← Finset.sum_div, hx.2, zero_div]

theorem normalizeCoordinates_fixed {p : ℕ} (k : Fin p) {x : Fin p → ℂ}
    (hx : x k = 1) : normalizeCoordinates k x = x := by
  funext j
  simp [normalizeCoordinates, hx]

theorem projective_mk_normalizeCoordinates {p : ℕ} (k : Fin p) {x : Fin p → ℂ}
    (hx : x k ≠ 0) (hx0 : x ≠ 0) (hn0 : normalizeCoordinates k x ≠ 0) :
    Projectivization.mk ℂ (normalizeCoordinates k x) hn0 = Projectivization.mk ℂ x hx0 := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ hn0 hx0).mpr
  refine ⟨(x k)⁻¹, ?_⟩
  funext j
  simp [normalizeCoordinates, div_eq_mul_inv, mul_comm]

def projectiveXEquivNormalized {p : ℕ} (k : Fin p) :
    ProjectiveX p ≃ (normalizedHyperplaneEquations k).locus where
  toFun q := ⟨normalizeCoordinates k q.val.rep, normalizeCoordinates_mem k q.property⟩
  invFun x :=
    let hx : x.val ≠ 0 := fun h => x.property.1 k (congrFun h k)
    ⟨Projectivization.mk ℂ x.val hx, (homogeneousZeroSum_projective_mk hx).mpr
      ⟨x.property.1, ((mem_normalizedHyperplane k x.val).mp x.property).2.1⟩⟩
  left_inv q := by
    apply Subtype.ext
    change Projectivization.mk ℂ (normalizeCoordinates k q.val.rep) _ = q.val
    rw [projective_mk_normalizeCoordinates k (q.property.1 k) q.val.rep_nonzero,
      Projectivization.mk_rep]
  right_inv x := by
    apply Subtype.ext
    change normalizeCoordinates k (Projectivization.mk ℂ x.val _).rep = x.val
    rw [normalizeCoordinates_projective_mk,
      normalizeCoordinates_fixed k ((mem_normalizedHyperplane k x.val).mp x.property).2.2]

end ModifiedCartan
