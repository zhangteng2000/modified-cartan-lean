import ModifiedCartan.TorusNullTopology
import Mathlib.RingTheory.Nullstellensatz

noncomputable section
set_option autoImplicit false
open Set Finset MvPolynomial
namespace ModifiedCartan

/-- Affine coordinates (x, x⁻¹, v) for the tangent space of the algebraic torus. -/
def torusJetCoordinates {N : ℕ} (x v : Fin N → ℂ) : Fin 3 × Fin N → ℂ :=
  fun a => if a.1 = 0 then x a.2 else if a.1 = 1 then (x a.2)⁻¹ else v a.2

def torusIntegerPowerPolynomial {N : ℕ} (j : Fin N) : ℤ → MvPolynomial (Fin 3 × Fin N) ℂ
  | .ofNat n => X (0, j) ^ n
  | .negSucc n => X (1, j) ^ (n + 1)

def torusMonomialPolynomial {N : ℕ} (α : Fin N → ℤ) : MvPolynomial (Fin 3 × Fin N) ℂ :=
  ∏ j, torusIntegerPowerPolynomial j (α j)

def torusMomentPolynomial {N q : ℕ} (P : LaurentData N q) (k : ℕ) :
    MvPolynomial (Fin 3 × Fin N) ℂ :=
  ∑ i, C (P.coefficient i) * torusMonomialPolynomial (P.exponent i) *
    (∑ j, C (P.exponent i j : ℂ) * (X (2, j) * X (1, j))) ^ k

theorem eval_torusIntegerPowerPolynomial {N : ℕ} (j : Fin N) (m : ℤ) (x v : Fin N → ℂ) :
    eval (torusJetCoordinates x v) (torusIntegerPowerPolynomial j m) = x j ^ m := by
  cases m with
  | ofNat n => simp [torusIntegerPowerPolynomial, torusJetCoordinates]
  | negSucc n => simp [torusIntegerPowerPolynomial, torusJetCoordinates, zpow_negSucc, inv_pow]

theorem eval_torusMonomialPolynomial {N : ℕ} (α : Fin N → ℤ) (x v : Fin N → ℂ) :
    eval (torusJetCoordinates x v) (torusMonomialPolynomial α) = laurentMonomial α x := by
  simp only [torusMonomialPolynomial, map_prod, eval_torusIntegerPowerPolynomial, laurentMonomial]

theorem eval_torusMomentPolynomial {N q : ℕ} (P : LaurentData N q) (k : ℕ) (x v : Fin N → ℂ) :
    eval (torusJetCoordinates x v) (torusMomentPolynomial P k) =
      ∑ i, P.orbitCoefficient x i * (P.orbitRate x v i) ^ k := by
  simp only [torusMomentPolynomial, map_sum, map_mul, map_pow, eval_C,
    eval_torusMonomialPolynomial, eval_X, torusJetCoordinates]
  simp only [Fin.reduceEq, ite_false, ite_true]
  simp only [LaurentData.orbitCoefficient, LaurentData.orbitRate, div_eq_mul_inv]

def torusInversePolynomial {N : ℕ} (j : Fin N) : MvPolynomial (Fin 3 × Fin N) ℂ :=
  X (0, j) * X (1, j) - 1

def TorusEquations.nullPolynomial {N : ℕ} (E : TorusEquations N) :
    (Fin N ⊕ ((i : Fin E.count) × Fin (E.terms i))) → MvPolynomial (Fin 3 × Fin N) ℂ
  | .inl j => torusInversePolynomial j
  | .inr ⟨i, k⟩ => torusMomentPolynomial (E.polynomial i) k

def TorusEquations.nullIdeal {N : ℕ} (E : TorusEquations N) : Ideal (MvPolynomial (Fin 3 × Fin N) ℂ) :=
  Ideal.span (range E.nullPolynomial)

/-- A concrete finite polynomial ideal cuts out zero directions in the affine
torus coordinates; the metric is not assumed to satisfy any algebraic axiom. -/
theorem torus_metric_zero_iff_polynomial_zeroLocus {N : ℕ} (E : TorusEquations N)
    {x v : Fin N → ℂ} (hx : x ∈ E.locus) :
    kobayashiRoyden E.locus x v = 0 ↔
      torusJetCoordinates x v ∈ MvPolynomial.zeroLocus ℂ E.nullIdeal := by
  rw [torus_locus_metric_zero_iff_moments E hx]
  rw [TorusEquations.nullIdeal, MvPolynomial.zeroLocus_span]
  change (∀ i (k : Fin (E.terms i)), _) ↔ ∀ P ∈ range E.nullPolynomial, _
  constructor
  · intro hm P hP
    obtain ⟨a, rfl⟩ := hP
    cases a with
    | inl j =>
      simp [TorusEquations.nullPolynomial, torusInversePolynomial, torusJetCoordinates, hx.1 j]
    | inr a =>
      simpa only [TorusEquations.nullPolynomial, MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id,
        eval_torusMomentPolynomial] using hm a.1 a.2
  · intro hp i k
    have h := hp _ (mem_range_self (Sum.inr ⟨i, k⟩))
    simpa only [TorusEquations.nullPolynomial, MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id,
      eval_torusMomentPolynomial] using h

end ModifiedCartan
