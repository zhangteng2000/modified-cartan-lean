import ModifiedCartan.NormalizedHyperplane
import Mathlib.Topology.Constructions

noncomputable section
set_option autoImplicit false
open Set Finset Topology
namespace ModifiedCartan

def normalizedDirectionSubspace {p : ℕ} (k : Fin p) : Submodule ℂ (Fin p → ℂ) where
  carrier := {v | v k = 0 ∧ ∑ j, v j = 0}
  zero_mem' := by simp
  add_mem' hu hv := by
    constructor
    · simp only [Pi.add_apply, hu.1, hv.1, add_zero]
    · simpa only [Pi.add_apply, Finset.sum_add_distrib, hu.2, hv.2, add_zero]
  smul_mem' c v hv := by
    constructor
    · change c * v k = 0
      rw [hv.1, mul_zero]
    · change ∑ j, c * v j = 0
      rw [← Finset.mul_sum, hv.2, mul_zero]

def normalizedSliceOpen {p : ℕ} (k : Fin p) (a : Fin p → ℂ) :
    TopologicalSpace.Opens (normalizedDirectionSubspace k) where
  carrier := {v | ∀ j, a j + v.val j ≠ 0}
  is_open' := by
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne_fun (continuous_const.add
      ((continuous_apply j).comp continuous_subtype_val)) continuous_const

theorem normalized_difference_mem {p : ℕ} (k : Fin p) {a x : Fin p → ℂ}
    (ha : a ∈ (normalizedHyperplaneEquations k).locus)
    (hx : x ∈ (normalizedHyperplaneEquations k).locus) :
    x - a ∈ normalizedDirectionSubspace k := by
  have ha' := (mem_normalizedHyperplane k a).mp ha
  have hx' := (mem_normalizedHyperplane k x).mp hx
  exact ⟨by simp [hx'.2.2, ha'.2.2],
    by simp only [Pi.sub_apply, Finset.sum_sub_distrib, hx'.2.1, ha'.2.1, sub_self]⟩

theorem normalized_add_direction_mem {p : ℕ} (k : Fin p) {a : Fin p → ℂ}
    (ha : a ∈ (normalizedHyperplaneEquations k).locus)
    (v : normalizedSliceOpen k a) :
    a + (v.val : Fin p → ℂ) ∈ (normalizedHyperplaneEquations k).locus := by
  have ha' := (mem_normalizedHyperplane k a).mp ha
  apply (mem_normalizedHyperplane k _).mpr
  exact ⟨v.property,
    by simp only [Pi.add_apply, Finset.sum_add_distrib, ha'.2.1, v.val.property.2, add_zero],
    by simp only [Pi.add_apply, ha'.2.2, v.val.property.1, add_zero]⟩

def normalizedHyperplaneHomeomorphOpen {p : ℕ} (k : Fin p) {a : Fin p → ℂ}
    (ha : a ∈ (normalizedHyperplaneEquations k).locus) :
    (normalizedHyperplaneEquations k).locus ≃ₜ normalizedSliceOpen k a where
  toFun x := ⟨⟨x.val - a, normalized_difference_mem k ha x.property⟩,
    fun j => by simpa using x.property.1 j⟩
  invFun v := ⟨a + (v.val : Fin p → ℂ), normalized_add_direction_mem k ha v⟩
  left_inv x := by
    apply Subtype.ext
    change a + (x.val - a) = x.val
    abel
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change a + (v.val : Fin p → ℂ) - a = (v.val : Fin p → ℂ)
    abel
  continuous_toFun := ((continuous_subtype_val.sub continuous_const).subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_const.add
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

end ModifiedCartan
