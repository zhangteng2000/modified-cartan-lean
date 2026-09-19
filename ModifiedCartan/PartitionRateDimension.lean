import ModifiedCartan.AdmissiblePartitions
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
set_option autoImplicit false
open Set Finset Module
namespace ModifiedCartan

/-- Logarithmic velocities constant on each part, with a chosen projective
normalization coordinate fixed. -/
def partitionRateSubspace {p : ℕ} (P : IndexPartition p) (k : Fin p) :
    Submodule ℂ (Fin p → ℂ) where
  carrier := {r | r k = 0 ∧ RatesConstantOnParts P r}
  zero_mem' := ⟨rfl, fun _ _ _ _ _ _ => rfl⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨by simp [ha.1, hb.1], ?_⟩
    intro I hI i hi j hj
    simp only [Pi.add_apply, ha.2 I hI i hi j hj, hb.2 I hI i hi j hj]
  smul_mem' := by
    intro c a ha
    refine ⟨by simp [ha.1], ?_⟩
    intro I hI i hi j hj
    simp only [Pi.smul_apply, ha.2 I hI i hi j hj]

theorem partitionRateSubspace_finrank_le {p : ℕ} (P : IndexPartition p) (k : Fin p) :
    finrank ℂ (partitionRateSubspace P k) ≤ P.parts.card - 1 := by
  classical
  let rep : P.parts → Fin p := fun I => Classical.choose (P.nonempty_of_mem_parts I.property)
  have hrep : ∀ I : P.parts, rep I ∈ I.val := fun I =>
    Classical.choose_spec (P.nonempty_of_mem_parts I.property)
  let key : P.parts := ⟨P.part k, P.part_mem.mpr (Finset.mem_univ k)⟩
  let S : Finset P.parts := Finset.univ.erase key
  let L : partitionRateSubspace P k →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun u I => u.val (rep I.val)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    intro a b hab
    apply Subtype.ext
    funext j
    let I : P.parts := ⟨P.part j, P.part_mem.mpr (Finset.mem_univ j)⟩
    have hj : j ∈ I.val := P.mem_part (Finset.mem_univ j)
    by_cases hI : I = key
    · have hk : k ∈ I.val := by
        rw [hI]
        exact P.mem_part (Finset.mem_univ k)
      exact (a.property.2 I.val I.property j hj k hk).trans
        (a.property.1.trans (b.property.1.symm.trans
          (b.property.2 I.val I.property j hj k hk).symm))
    · have hIS : I ∈ S := by simp [S, hI]
      have hv := congrFun hab ⟨I, hIS⟩
      change a.val (rep I) = b.val (rep I) at hv
      exact (a.property.2 I.val I.property j hj (rep I) (hrep I)).trans
        (hv.trans (b.property.2 I.val I.property j hj (rep I) (hrep I)).symm)
  have hdim := LinearMap.finrank_le_finrank_of_injective hL
  have hcard : finrank ℂ (S → ℂ) = P.parts.card - 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [S]
  exact hdim.trans_eq hcard

theorem admissible_rate_finrank_bound {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) {P : IndexPartition p} (hP : IsAdmissiblePartition x P)
    (k : Fin p) : finrank ℂ (partitionRateSubspace P k) ≤ p / 2 - 1 :=
  (partitionRateSubspace_finrank_le P k).trans
    (Nat.sub_le_sub_right (admissible_parts_card_le_half hx hP) 1)

end ModifiedCartan
