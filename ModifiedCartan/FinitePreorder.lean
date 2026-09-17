import ModifiedCartan.Stabilization
import Mathlib.Order.Preorder.Finite

noncomputable section
set_option autoImplicit false
open Finset
namespace ModifiedCartan

/-- Explicit preorders allow comparison of different orders on the same finite type. -/
structure FinitePreorder (α : Type*) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

def PreorderMaximal {α : Type*} (R : FinitePreorder α) (x : α) : Prop :=
  ∀ y, R.rel x y → R.rel y x

def preorderClass {α : Type*} [Fintype α] (R : FinitePreorder α) (x : α) : Finset α :=
  @Finset.filter α (fun y => R.rel x y ∧ R.rel y x) (Classical.decPred _) univ

def maximalClasses {α : Type*} [Fintype α] (R : FinitePreorder α) : Finset (Finset α) := by
  classical
  exact (univ.filter (PreorderMaximal R)).image (preorderClass R)

theorem mem_preorderClass {α : Type*} [Fintype α] {R : FinitePreorder α} {x y : α} :
    y ∈ preorderClass R x ↔ R.rel x y ∧ R.rel y x := by
  classical
  simp [preorderClass]

theorem mem_preorderClass_self {α : Type*} [Fintype α] (R : FinitePreorder α) (x : α) :
    x ∈ preorderClass R x := mem_preorderClass.mpr ⟨R.refl x, R.refl x⟩

theorem preorderClass_eq_iff {α : Type*} [Fintype α] (R : FinitePreorder α) (x y : α) :
    preorderClass R x = preorderClass R y ↔ R.rel x y ∧ R.rel y x := by
  classical
  constructor
  · intro h
    have hy := mem_preorderClass_self R y
    rw [← h] at hy
    exact mem_preorderClass.mp hy
  · rintro ⟨hxy, hyx⟩
    ext z
    simp only [mem_preorderClass]
    exact ⟨fun ⟨hxz, hzx⟩ => ⟨R.trans hyx hxz, R.trans hzx hxy⟩,
      fun ⟨hyz, hzy⟩ => ⟨R.trans hxy hyz, R.trans hzy hyx⟩⟩

theorem exists_preorderMaximal_above {α : Type*} [Fintype α] (R : FinitePreorder α) (x : α) :
    ∃ y, R.rel x y ∧ PreorderMaximal R y := by
  classical
  let : Preorder α := { le := R.rel, le_refl := R.refl, le_trans := fun _ _ _ => R.trans }
  obtain ⟨y, hxy, _, hy⟩ := (univ : Finset α).exists_le_maximal (mem_univ x)
  exact ⟨y, hxy, fun z hz => hy (mem_univ z) hz⟩

theorem mem_maximalClasses {α : Type*} [Fintype α] {R : FinitePreorder α} {C : Finset α} :
    C ∈ maximalClasses R ↔ ∃ x, PreorderMaximal R x ∧ preorderClass R x = C := by
  classical
  simp [maximalClasses]

theorem preorderMaximal_of_mem_class {α : Type*} [Fintype α] {R : FinitePreorder α}
    {x y : α} (hx : PreorderMaximal R x) (hy : y ∈ preorderClass R x) :
    PreorderMaximal R y := by
  obtain ⟨hxy, hyx⟩ := mem_preorderClass.mp hy
  intro z hyz
  exact R.trans (hx z (R.trans hxy hyz)) hxy

theorem maximalClasses_nonempty {α : Type*} [Fintype α] [Nonempty α] (R : FinitePreorder α) :
    (maximalClasses R).Nonempty := by
  obtain ⟨y, _, hy⟩ := exists_preorderMaximal_above R (Classical.arbitrary α)
  exact ⟨preorderClass R y, mem_maximalClasses.mpr ⟨y, hy, rfl⟩⟩

theorem maximalClasses_card_le {α : Type*} [Fintype α] (R : FinitePreorder α) :
    (maximalClasses R).card ≤ Fintype.card α := by
  classical
  exact (card_image_le).trans (card_filter_le _ _)

/-- Every new maximal class contains a whole old maximal class. -/
theorem maximalClass_contains_old {α : Type*} [Fintype α]
    {R S : FinitePreorder α} (hRS : ∀ x y, R.rel x y → S.rel x y)
    {C : Finset α} (hC : C ∈ maximalClasses S) :
    ∃ B ∈ maximalClasses R, B ⊆ C := by
  obtain ⟨x, hx, rfl⟩ := mem_maximalClasses.mp hC
  obtain ⟨y, hxy, hy⟩ := exists_preorderMaximal_above R x
  refine ⟨preorderClass R y, mem_maximalClasses.mpr ⟨y, hy, rfl⟩, ?_⟩
  intro z hz
  obtain ⟨hyz, hzy⟩ := mem_preorderClass.mp hz
  exact mem_preorderClass.mpr ⟨S.trans (hRS _ _ hxy) (hRS _ _ hyz),
    S.trans (hRS _ _ hzy) (hx y (hRS _ _ hxy))⟩

theorem maximalClasses_eq_of_common {α : Type*} [Fintype α]
    {R : FinitePreorder α} {B C : Finset α} (hB : B ∈ maximalClasses R)
    (hC : C ∈ maximalClasses R) {x : α} (hxB : x ∈ B) (hxC : x ∈ C) : B = C := by
  obtain ⟨b, _, rfl⟩ := mem_maximalClasses.mp hB
  obtain ⟨c, _, rfl⟩ := mem_maximalClasses.mp hC
  obtain ⟨hbx, hxb⟩ := mem_preorderClass.mp hxB
  obtain ⟨hcx, hxc⟩ := mem_preorderClass.mp hxC
  exact (preorderClass_eq_iff R b c).mpr ⟨R.trans hbx hxc, R.trans hcx hxb⟩

/-- Choose an old maximal class inside each new maximal class; the choice is injective. -/
theorem maximalClasses_injection {α : Type*} [Fintype α]
    {R S : FinitePreorder α} (hRS : ∀ x y, R.rel x y → S.rel x y) :
    ∃ F : (maximalClasses S) → (maximalClasses R), Function.Injective F ∧
      ∀ C, (F C).val ⊆ C.val := by
  classical
  have hex : ∀ C : maximalClasses S, ∃ B : maximalClasses R, B.val ⊆ C.val := by
    intro C
    obtain ⟨B, hB, hBC⟩ := maximalClass_contains_old hRS C.property
    exact ⟨⟨B, hB⟩, hBC⟩
  choose F hF using hex
  refine ⟨F, ?_, hF⟩
  intro C D heq
  obtain ⟨x, hx, hclass⟩ := mem_maximalClasses.mp (F C).property
  have hmem : x ∈ (F C).val := hclass ▸ mem_preorderClass_self R x
  have hmemD : x ∈ (F D).val := heq ▸ hmem
  apply Subtype.ext
  exact maximalClasses_eq_of_common C.property D.property (hF C hmem) (hF D hmemD)

theorem maximalClasses_card_antitone {α : Type*} [Fintype α]
    {R S : FinitePreorder α} (hRS : ∀ x y, R.rel x y → S.rel x y) :
    (maximalClasses S).card ≤ (maximalClasses R).card := by
  classical
  obtain ⟨F, hF, _⟩ := maximalClasses_injection hRS
  simpa using Fintype.card_le_of_injective F hF

/-- If the number of maximal classes stays unchanged, every old maximal class
is contained in a new maximal class. -/
theorem old_maximalClass_survives {α : Type*} [Fintype α]
    {R S : FinitePreorder α} (hRS : ∀ x y, R.rel x y → S.rel x y)
    (hcard : (maximalClasses R).card = (maximalClasses S).card)
    {B : Finset α} (hB : B ∈ maximalClasses R) :
    ∃ C ∈ maximalClasses S, B ⊆ C := by
  classical
  obtain ⟨F, hF, hsub⟩ := maximalClasses_injection hRS
  have hsurj : Function.Surjective F := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective F hF h
    simp only [Fintype.card_coe] at hlt
    omega
  obtain ⟨C, hC⟩ := hsurj ⟨B, hB⟩
  exact ⟨C.val, C.property, by simpa only [hC] using hsub C⟩

theorem maximalClasses_bijection {α : Type*} [Fintype α]
    {R S : FinitePreorder α} (hRS : ∀ x y, R.rel x y → S.rel x y)
    (hcard : (maximalClasses R).card = (maximalClasses S).card) :
    ∃ F : (maximalClasses S) → (maximalClasses R), Function.Bijective F ∧
      ∀ C, (F C).val ⊆ C.val := by
  classical
  obtain ⟨F, hF, hsub⟩ := maximalClasses_injection hRS
  refine ⟨F, ⟨hF, ?_⟩, hsub⟩
  by_contra h
  have hlt := Fintype.card_lt_of_injective_not_surjective F hF h
  simp only [Fintype.card_coe] at hlt
  omega

theorem old_maximals_incomparable {α : Type*} [Fintype α]
    {R S : FinitePreorder α} (hRS : ∀ x y, R.rel x y → S.rel x y)
    (hcard : (maximalClasses R).card = (maximalClasses S).card)
    {x y : α} (hx : PreorderMaximal R x) (hy : PreorderMaximal R y)
    (hne : ¬ (R.rel x y ∧ R.rel y x)) : ¬ S.rel x y ∧ ¬ S.rel y x := by
  classical
  obtain ⟨F, hF, hsub⟩ := maximalClasses_bijection hRS hcard
  obtain ⟨C, hC⟩ := hF.2 ⟨preorderClass R x, mem_maximalClasses.mpr ⟨x, hx, rfl⟩⟩
  obtain ⟨D, hD⟩ := hF.2 ⟨preorderClass R y, mem_maximalClasses.mpr ⟨y, hy, rfl⟩⟩
  have hxC : x ∈ C.val := hsub C (by rw [hC]; exact mem_preorderClass_self R x)
  have hyD : y ∈ D.val := hsub D (by rw [hD]; exact mem_preorderClass_self R y)
  have hCD : C ≠ D := by
    intro h
    have he : preorderClass R x = preorderClass R y := by
      exact congrArg Subtype.val (hC.symm.trans ((congrArg F h).trans hD))
    exact hne ((preorderClass_eq_iff R x y).mp he)
  obtain ⟨c, hc, hcC⟩ := mem_maximalClasses.mp C.property
  obtain ⟨d, hd, hdD⟩ := mem_maximalClasses.mp D.property
  have hxc := mem_preorderClass.mp (hcC ▸ hxC : x ∈ preorderClass S c)
  have hyd := mem_preorderClass.mp (hdD ▸ hyD : y ∈ preorderClass S d)
  have hxmax : PreorderMaximal S x :=
    preorderMaximal_of_mem_class hc (mem_preorderClass.mpr hxc)
  have hymax : PreorderMaximal S y :=
    preorderMaximal_of_mem_class hd (mem_preorderClass.mpr hyd)
  have hnot : ¬ (S.rel x y ∧ S.rel y x) := by
    rintro ⟨hxy, hyx⟩
    apply hCD
    apply Subtype.ext
    rw [← hcC, ← hdD]
    exact (preorderClass_eq_iff S c d).mpr
      ⟨S.trans hxc.1 (S.trans hxy hyd.2), S.trans hyd.1 (S.trans hyx hxc.2)⟩
  exact ⟨fun hxy => hnot ⟨hxy, hxmax y hxy⟩,
    fun hyx => hnot ⟨hymax x hyx, hyx⟩⟩

/-- The full finite-order component of manuscript Lemma `lem:stabilization`. -/
theorem finite_preorder_stabilization {p : ℕ} (hp : 1 ≤ p)
    (R : ℕ → FinitePreorder (Fin p))
    (hmono : ∀ k, k + 1 < p → ∀ x y, (R k).rel x y → (R (k + 1)).rel x y) :
    ∃ l, l < p ∧ ((maximalClasses (R l)).card = 1 ∨
      (l + 1 < p ∧ ∀ x y, PreorderMaximal (R l) x → PreorderMaximal (R l) y →
        ¬ ((R l).rel x y ∧ (R l).rel y x) →
        ¬ (R (l + 1)).rel x y ∧ ¬ (R (l + 1)).rel y x)) := by
  have : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  let t : ℕ → ℕ := fun k => (maximalClasses (R k)).card
  have hpos : ∀ k, k < p → 1 ≤ t k := by
    intro k _
    exact card_pos.mpr (maximalClasses_nonempty (R k))
  have hbound : t 0 ≤ p := by simpa [t] using maximalClasses_card_le (R 0)
  have hcount : ∀ k, k + 1 < p → t (k + 1) ≤ t k :=
    fun k hk => maximalClasses_card_antitone (hmono k hk)
  rcases count_stabilization hp t hpos hbound hcount with ⟨l, hl, htl⟩ | ⟨l, hl, heq⟩
  · exact ⟨l, hl, Or.inl htl⟩
  · exact ⟨l, by omega, Or.inr ⟨hl, fun _ _ hx hy hne =>
      old_maximals_incomparable (hmono l hl) heq hx hy hne⟩⟩

end ModifiedCartan
