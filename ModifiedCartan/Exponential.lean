import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace ModifiedCartan

def exponentialSum {n : ℕ} (a rate : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, a j * Complex.exp (rate j * z)

def moment {n : ℕ} (a rate : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ j, a j * rate j ^ k

/-- The finite Vandermonde step used in Section 6. -/
theorem coefficients_zero_of_moments {n : ℕ} {a rate : Fin n → ℂ}
    (hrate : Function.Injective rate) (hm : ∀ k : Fin n, moment a rate k = 0) : a = 0 := by
  exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hrate hm

theorem exponentialSum_iteratedDeriv {n : ℕ} (a rate : Fin n → ℂ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (exponentialSum a rate) z =
      ∑ j, a j * rate j ^ k * Complex.exp (rate j * z) := by
  unfold exponentialSum
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
    ring
  · intro j _
    fun_prop

theorem exponentialSum_derivatives_at_zero {n : ℕ} (a rate : Fin n → ℂ) (k : ℕ) :
    iteratedDeriv k (exponentialSum a rate) 0 = moment a rate k := by
  simp [exponentialSum_iteratedDeriv, moment]

theorem moments_zero_of_exponentialSum_zero {n : ℕ} {a rate : Fin n → ℂ}
    (h : ∀ z, exponentialSum a rate z = 0) (k : ℕ) : moment a rate k = 0 := by
  have heq : exponentialSum a rate = fun _ => 0 := funext h
  rw [← exponentialSum_derivatives_at_zero, heq]
  simp

theorem exponentialSum_zero_iff_coefficients {n : ℕ} {a rate : Fin n → ℂ}
    (hrate : Function.Injective rate) :
    (∀ z, exponentialSum a rate z = 0) ↔ a = 0 := by
  constructor
  · intro h
    exact coefficients_zero_of_moments hrate (fun k => moments_zero_of_exponentialSum_zero h k)
  · intro ha z
    simp [exponentialSum, ha]

/-- An entire exponential sum with distinct rates is identically zero iff its first n jets vanish. -/
theorem exponentialSum_zero_iff_finite_moments {n : ℕ} {a rate : Fin n → ℂ}
    (hrate : Function.Injective rate) :
    (∀ z, exponentialSum a rate z = 0) ↔ ∀ k : Fin n, moment a rate k = 0 := by
  constructor
  · intro h k
    exact moments_zero_of_exponentialSum_zero h k
  · intro h
    exact (exponentialSum_zero_iff_coefficients hrate).mpr (coefficients_zero_of_moments hrate h)

def groupedCoefficient {n d : ℕ} (a : Fin n → ℂ) (group : Fin n → Fin d) (i : Fin d) : ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j => group j = i), a j

theorem exponentialSum_grouping {n d : ℕ} (a : Fin n → ℂ)
    (group : Fin n → Fin d) (μ : Fin d → ℂ) (z : ℂ) :
    exponentialSum a (μ ∘ group) z = exponentialSum (groupedCoefficient a group) μ z := by
  unfold exponentialSum groupedCoefficient
  simp_rw [Finset.sum_mul]
  symm
  calc
    _ = ∑ i : Fin d, ∑ j ∈ Finset.univ.filter (fun j => group j = i),
        a j * Complex.exp (μ (group j) * z) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_filter] at hj
      rw [hj.2]
    _ = _ := by simp [Finset.sum_fiberwise]

theorem exponentialSum_zero_iff_grouped {n d : ℕ} (a : Fin n → ℂ)
    (group : Fin n → Fin d) {μ : Fin d → ℂ} (hμ : Function.Injective μ) :
    (∀ z, exponentialSum a (μ ∘ group) z = 0) ↔ groupedCoefficient a group = 0 := by
  simp_rw [exponentialSum_grouping]
  exact exponentialSum_zero_iff_coefficients hμ

theorem moment_grouping {n d : ℕ} (a : Fin n → ℂ)
    (group : Fin n → Fin d) (μ : Fin d → ℂ) (k : ℕ) :
    moment a (μ ∘ group) k = moment (groupedCoefficient a group) μ k := by
  unfold moment groupedCoefficient
  simp_rw [Finset.sum_mul]
  symm
  calc
    _ = ∑ i : Fin d, ∑ j ∈ Finset.univ.filter (fun j => group j = i),
        a j * μ (group j) ^ k := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_filter] at hj
      rw [hj.2]
    _ = _ := by simp [Finset.sum_fiberwise]

/-- Proposition 6.1's finite-equation criterion, with arbitrary repeated rates.
There are n summands, so the first n moments suffice even when fewer than
n distinct rates occur. -/
theorem exponentialSum_zero_iff_moments {n : ℕ} (a rate : Fin n → ℂ) :
    (∀ z, exponentialSum a rate z = 0) ↔ ∀ k : Fin n, moment a rate k = 0 := by
  classical
  constructor
  · intro h k
    exact moments_zero_of_exponentialSum_zero h k
  · intro hm
    let S : Finset ℂ := Finset.univ.image rate
    let e : S ≃ Fin S.card := S.equivFin
    let group : Fin n → Fin S.card := fun j => e ⟨rate j, by simp [S]⟩
    let μ : Fin S.card → ℂ := fun j => (e.symm j).val
    have hμ : Function.Injective μ := by
      intro i j hij
      exact e.symm.injective (Subtype.ext hij)
    have heq : μ ∘ group = rate := by
      funext j
      simp [μ, group]
    have hcard : S.card ≤ n := by
      simpa [S] using (Finset.card_image_le (s := Finset.univ) (f := rate))
    have hgroup : ∀ k : Fin S.card, moment (groupedCoefficient a group) μ k = 0 := by
      intro k
      rw [← moment_grouping, heq]
      exact hm ⟨k.val, lt_of_lt_of_le k.isLt hcard⟩
    have hzero := (exponentialSum_zero_iff_finite_moments hμ).mpr hgroup
    intro z
    rw [← heq, exponentialSum_grouping]
    exact hzero z

/-- Coordinatewise exponential orbit from Theorem `thm:torus-zero`. -/
def exponentialOrbit {N : ℕ} (x v : Fin N → ℂ) (z : ℂ) : Fin N → ℂ :=
  fun j => x j * Complex.exp ((v j / x j) * z)

theorem exponentialOrbit_at_zero {N : ℕ} (x v : Fin N → ℂ) :
    exponentialOrbit x v 0 = x := by
  funext j
  simp [exponentialOrbit]

theorem exponentialOrbit_nonzero {N : ℕ} {x v : Fin N → ℂ}
    (hx : ∀ j, x j ≠ 0) (z : ℂ) (j : Fin N) : exponentialOrbit x v z j ≠ 0 :=
  mul_ne_zero (hx j) (Complex.exp_ne_zero _)

theorem exponentialOrbit_hasDerivAt {N : ℕ} {x v : Fin N → ℂ}
    (hx : ∀ j, x j ≠ 0) (j : Fin N) :
    HasDerivAt (fun z => exponentialOrbit x v z j) (v j) 0 := by
  have h := (((hasDerivAt_id (0 : ℂ)).const_mul (v j / x j)).cexp.const_mul (x j))
  have he : x j * (v j / x j) = v j := by field_simp [hx j]
  simpa [exponentialOrbit, he] using h

end ModifiedCartan
