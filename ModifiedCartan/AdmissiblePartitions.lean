import ModifiedCartan.Exponential
import Mathlib.Order.Partition.Finpartition

noncomputable section
set_option autoImplicit false
open Set Finset
namespace ModifiedCartan

abbrev IndexPartition (p : ℕ) := Finpartition (Finset.univ : Finset (Fin p))

def IsAdmissiblePartition {p : ℕ} (x : Fin p → ℂ) (P : IndexPartition p) : Prop :=
  ∀ I ∈ P.parts, ∑ j ∈ I, x j = 0

def RatesConstantOnParts {p : ℕ} (P : IndexPartition p) (r : Fin p → ℂ) : Prop :=
  ∀ I ∈ P.parts, ∀ i ∈ I, ∀ j ∈ I, r i = r j

theorem exponentialSum_zero_fiber_coefficients {p : ℕ} {a r : Fin p → ℂ}
    (h : ∀ z, exponentialSum a r z = 0) (ν : ℂ) :
    ∑ j ∈ Finset.univ.filter (fun j => r j = ν), a j = 0 := by
  classical
  let S : Finset ℂ := Finset.univ.image r
  by_cases hν : ν ∈ S
  · let e : S ≃ Fin S.card := S.equivFin
    let group : Fin p → Fin S.card := fun j => e ⟨r j, by simp [S]⟩
    let μ : Fin S.card → ℂ := fun j => (e.symm j).val
    have hμ : Function.Injective μ := fun i j hij => e.symm.injective (Subtype.ext hij)
    have heq : μ ∘ group = r := by funext j; simp [μ, group]
    have hgroup := (exponentialSum_zero_iff_grouped a group hμ).mp (heq ▸ h)
    have hcoeff := congrFun hgroup (e ⟨ν, hν⟩)
    have hfiber : ∀ j, group j = e ⟨ν, hν⟩ ↔ r j = ν := by
      intro j
      change e ⟨r j, _⟩ = e ⟨ν, hν⟩ ↔ r j = ν
      rw [e.injective.eq_iff, Subtype.mk.injEq]
    simpa only [groupedCoefficient, hfiber, Pi.zero_apply] using hcoeff
  · apply Finset.sum_eq_zero
    intro j hj
    have hjν := (Finset.mem_filter.mp hj).2
    exact False.elim (hν (Finset.mem_image.mpr ⟨j, mem_univ _, hjν⟩))

theorem indexPartition_sum {p : ℕ} (P : IndexPartition p) (b : Fin p → ℂ) :
    ∑ j, b j = ∑ I ∈ P.parts, ∑ j ∈ I, b j := by
  calc
    _ = ∑ j ∈ P.parts.biUnion id, b j :=
      congrArg (fun S : Finset (Fin p) => ∑ j ∈ S, b j) P.biUnion_parts.symm
    _ = _ := Finset.sum_biUnion P.supIndep.pairwiseDisjoint

theorem exponentialSum_zero_of_admissible {p : ℕ} {x r : Fin p → ℂ}
    {P : IndexPartition p} (hP : IsAdmissiblePartition x P)
    (hr : RatesConstantOnParts P r) : ∀ z, exponentialSum x r z = 0 := by
  intro z
  rw [exponentialSum, indexPartition_sum P]
  apply Finset.sum_eq_zero
  intro I hI
  obtain ⟨k, hk⟩ := P.nonempty_of_mem_parts hI
  calc
    _ = ∑ j ∈ I, x j * Complex.exp (r k * z) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hr I hI j hj k hk]
    _ = (∑ j ∈ I, x j) * Complex.exp (r k * z) := by rw [Finset.sum_mul]
    _ = 0 := by rw [hP I hI, zero_mul]

def ratePartition {p : ℕ} (r : Fin p → ℂ) : IndexPartition p := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker r)

theorem ratePartition_part {p : ℕ} (r : Fin p → ℂ) (i : Fin p) :
    (ratePartition r).part i = Finset.univ.filter (fun j => r j = r i) := by
  classical
  ext j
  simp only [ratePartition, Finpartition.mem_part_ofSetoid_iff_rel, Setoid.ker_def,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm

theorem ratePartition_constant {p : ℕ} (r : Fin p → ℂ) :
    RatesConstantOnParts (ratePartition r) r := by
  intro I hI i hi j hj
  have hpart := (ratePartition r).part_eq_of_mem hI hi
  rw [ratePartition_part] at hpart
  have hj' : j ∈ Finset.univ.filter (fun j => r j = r i) := hpart.symm ▸ hj
  exact (Finset.mem_filter.mp hj').2.symm

theorem ratePartition_admissible {p : ℕ} {x r : Fin p → ℂ}
    (h : ∀ z, exponentialSum x r z = 0) :
    IsAdmissiblePartition x (ratePartition r) := by
  intro I hI
  obtain ⟨i, hi⟩ := (ratePartition r).nonempty_of_mem_parts hI
  rw [← (ratePartition r).part_eq_of_mem hI hi, ratePartition_part]
  exact exponentialSum_zero_fiber_coefficients h (r i)

theorem exponentialSum_zero_iff_admissible_partition {p : ℕ} (x r : Fin p → ℂ) :
    (∀ z, exponentialSum x r z = 0) ↔
      ∃ P : IndexPartition p, IsAdmissiblePartition x P ∧ RatesConstantOnParts P r := by
  exact ⟨fun h => ⟨ratePartition r, ratePartition_admissible h, ratePartition_constant r⟩,
    fun ⟨_, hP, hr⟩ => exponentialSum_zero_of_admissible hP hr⟩

theorem admissible_part_card_ge_two {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) {P : IndexPartition p} (hP : IsAdmissiblePartition x P)
    {I : Finset (Fin p)} (hI : I ∈ P.parts) : 2 ≤ I.card := by
  have hpos := (P.nonempty_of_mem_parts hI).card_pos
  by_contra hn
  have hcard : I.card = 1 := by omega
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
  have h := hP _ hI
  exact hx j (by simpa using h)

theorem admissible_parts_card_le_half {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) {P : IndexPartition p} (hP : IsAdmissiblePartition x P) :
    P.parts.card ≤ p / 2 := by
  have h : 2 * P.parts.card ≤ p := by
    calc
      _ = ∑ I ∈ P.parts, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ I ∈ P.parts, I.card := Finset.sum_le_sum (fun I hI =>
        admissible_part_card_ge_two hx hP hI)
      _ = p := by simpa using P.sum_card_parts
  omega

end ModifiedCartan
