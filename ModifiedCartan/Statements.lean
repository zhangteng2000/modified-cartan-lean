import ModifiedCartan.Basic
import ModifiedCartan.Radii
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Precise proof targets from the supplied manuscript.
Every declaration in this module is a DEFINITION of a proposition, not a proof.
In particular, this module does not introduce these propositions as axioms.
-/
noncomputable section
open scoped BigOperators
namespace ModifiedCartan

def diskSupNorm (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' Metric.closedBall (0 : ℂ) r)

def wronskian {m : ℕ} (g : Fin m → ℂ → ℂ) (z : ℂ) : ℂ :=
  Matrix.det (.of fun i j : Fin m => iteratedDeriv (i : ℕ) (g j) z)

def coefficientNormSq {m : ℕ} (c : Fin m → ℂ) : ℝ := ∑ j, ‖c j‖ ^ 2

def leastCombinationNorm {m : ℕ} (g : Fin m → ℂ → ℂ) (r : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ c : Fin m → ℂ, coefficientNormSq c = 1 ∧
    v = diskSupNorm (fun z => ∑ j, c j * g j z) r}

/-- Theorem `thm:main`. OPEN proof target. -/
def PartitionTheorem : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ PartitionProperty p (disk ε)

/-- Lemma 2.1. Proved by `cartanCircleEstimate_proved` in CartanCircle.lean. -/
def CartanCircleEstimate : Prop :=
  ∀ a b c : ℝ, 0 < a → a < b → b < c → c < 1 →
  ∃ γ : ℝ, 0 < γ ∧ ∀ (F : ℂ → ℂ) (t : ℝ),
    DifferentiableOn ℂ F (disk 1) → (∀ z ∈ disk 1, ‖F z‖ ≤ 1) →
    0 < t → t ≤ 1 → t ≤ diskSupNorm F a →
    ∃ ρ : ℝ, b < ρ ∧ ρ < c ∧ ∀ z : ℂ, ‖z‖ = ρ → t ^ γ ≤ ‖F z‖

/-- Proposition 2.2, proved by `quantitativeWronskian_proved`. -/
def QuantitativeWronskian : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ a b : ℝ, 0 < a → a < b → b < 1 →
  ∃ c K : ℝ, 0 < c ∧ (m : ℝ) ≤ K ∧ ∀ g : Fin m → ℂ → ℂ,
    (∀ j, DifferentiableOn ℂ (g j) (disk 1)) →
    (∀ j z, z ∈ disk 1 → ‖g j z‖ ≤ 1) →
    c * (leastCombinationNorm g a) ^ K ≤ diskSupNorm (wronskian g) b

/-- Lemma 2.4. Proved as `growthLemma_proved` in Growth.lean. -/
def GrowthLemma : Prop :=
  ∀ (M : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn M (Set.Icc a b) →
    MonotoneOn M (Set.Icc a b) → (∀ x ∈ Set.Icc a b, 0 < M x) →
    2 / M a < b - a →
    ∃ ρ : ℝ, a ≤ ρ ∧ ρ < b ∧ ρ + 1 / M ρ < b ∧
      M (ρ + 1 / M ρ) ≤ 2 * M ρ

def AbsorptionAt (m : ℕ) (U : Set ℂ) : Prop :=
  ∀ (A a : Family m) (s : ℂ → ℂ), UnitFamily A →
    (∀ i n, DifferentiableOn ℂ (a i n) (disk 1)) →
    (∀ i, CompactConvergence (fun n z => a i n z / A i n z) (fun _ => 0) (disk 1)) →
    CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1) →
    (∃ z ∈ disk 1, s z ≠ 0) →
    ∃ i : Fin m, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => (A i (φ n) z)⁻¹) (fun _ => 0) U

/-- Proposition 3.1, existence form. OPEN proof target. -/
def AbsorptionTheorem : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ AbsorptionAt m (disk r)

/-- Poincare distance with length element 2 |dz|/(1-|z|^2).
Only used with z,w in the unit disk. -/
def hyperbolicDistance (z w : ℂ) : ℝ :=
  let q := ‖(z - w) / (1 - star w * z)‖
  Real.log ((1 + q) / (1 - q))

def HasHyperbolicDiameterLE (U : Set ℂ) (d : ℝ) : Prop :=
  ∀ z ∈ U, ∀ w ∈ U, hyperbolicDistance z w ≤ d

/-- Theorem `thm:sharp-five`, including disconnected open sets and the endpoint. OPEN proof target. -/
def SharpFiveTheorem : Prop :=
  ∀ U : Set ℂ, U.Nonempty → IsOpen U → U ⊆ disk 1 →
    HasHyperbolicDiameterLE U (Real.log 3) → PartitionProperty 5 U

/-- Proposition 5.3. OPEN proof target. -/
def SharpTwoAbsorption : Prop :=
  ∀ U : Set ℂ, U.Nonempty → IsOpen U → U ⊆ disk 1 →
    HasHyperbolicDiameterLE U (Real.log 3) → AbsorptionAt 2 U

def optimalRadius (p : ℕ) : ℝ :=
  sSup {r : ℝ | 0 < r ∧ r < 1 ∧ PartitionProperty p (disk r)}

/-- Numerical equality for the genuine partition property. OPEN proof target. -/
def OptimalFiveRadius : Prop := optimalRadius 5 = sharpRadius

end ModifiedCartan
