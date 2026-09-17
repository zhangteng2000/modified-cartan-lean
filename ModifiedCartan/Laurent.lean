import ModifiedCartan.Exponential

noncomputable section
open scoped BigOperators
namespace ModifiedCartan

/-- A finite presentation of a Laurent polynomial. Repeated exponents are allowed. -/
structure LaurentData (N q : ℕ) where
  coefficient : Fin q → ℂ
  exponent : Fin q → Fin N → ℤ

def laurentMonomial {N : ℕ} (α : Fin N → ℤ) (x : Fin N → ℂ) : ℂ :=
  ∏ j, x j ^ α j

def LaurentData.eval {N q : ℕ} (P : LaurentData N q) (x : Fin N → ℂ) : ℂ :=
  ∑ i, P.coefficient i * laurentMonomial (P.exponent i) x

def LaurentData.orbitCoefficient {N q : ℕ} (P : LaurentData N q)
    (x : Fin N → ℂ) (i : Fin q) : ℂ :=
  P.coefficient i * laurentMonomial (P.exponent i) x

def LaurentData.orbitRate {N q : ℕ} (P : LaurentData N q)
    (x v : Fin N → ℂ) (i : Fin q) : ℂ :=
  ∑ j, (P.exponent i j : ℂ) * (v j / x j)

theorem laurentMonomial_on_orbit {N : ℕ} (α : Fin N → ℤ) (x v : Fin N → ℂ) (z : ℂ) :
    laurentMonomial α (exponentialOrbit x v z) =
      laurentMonomial α x * Complex.exp ((∑ j, (α j : ℂ) * (v j / x j)) * z) := by
  unfold laurentMonomial exponentialOrbit
  simp_rw [mul_zpow]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [← Complex.exp_int_mul]
  rw [Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  ring

theorem laurent_eval_on_orbit {N q : ℕ} (P : LaurentData N q)
    (x v : Fin N → ℂ) (z : ℂ) :
    P.eval (exponentialOrbit x v z) =
      exponentialSum (P.orbitCoefficient x) (P.orbitRate x v) z := by
  unfold LaurentData.eval exponentialSum LaurentData.orbitCoefficient LaurentData.orbitRate
  apply Finset.sum_congr rfl
  intro i _
  rw [laurentMonomial_on_orbit]
  ring

/-- The actual Laurent-polynomial finite-equation criterion in Proposition 6.1. -/
theorem laurent_orbit_zero_iff_finite_equations {N q : ℕ} (P : LaurentData N q)
    (x v : Fin N → ℂ) :
    (∀ z : ℂ, P.eval (exponentialOrbit x v z) = 0) ↔
    ∀ k : Fin q, ∑ i, P.coefficient i * laurentMonomial (P.exponent i) x *
      (∑ j, (P.exponent i j : ℂ) * (v j / x j)) ^ (k : ℕ) = 0 := by
  simp_rw [laurent_eval_on_orbit]
  exact exponentialSum_zero_iff_moments (P.orbitCoefficient x) (P.orbitRate x v)

end ModifiedCartan
