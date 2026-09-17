import ModifiedCartan.Statements
import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

/-! Exact remaining analytic proof targets. These are proposition definitions,
not assumed mathematical facts. In particular, the explicit absorption target
includes the obligation to produce valid Wronskian exponents. -/
noncomputable section
open scoped BigOperators
open Real
namespace ModifiedCartan

/-- The manuscript's m(r,h), using mathlib's Nevanlinna proximity function. -/
def proximityMean (h : ℂ → ℂ) (r : ℝ) : ℝ := ValueDistribution.proximity h ⊤ r

/-- `lem:logderivative`, including its dependence on all fixed radii and k. OPEN. -/
def LogDerivativeEstimate : Prop :=
  ∀ (α rMinus rPlus : ℝ) (k : ℕ),
    0 < α → α < rMinus → rMinus < rPlus → rPlus < 1 → 1 ≤ k →
    ∃ C : ℝ, ∀ (h : ℂ → ℂ) (τ r R : ℝ),
      DifferentiableOn ℂ h (disk 1) → 0 < τ → τ ≤ diskSupNorm h α →
      rMinus ≤ r → r < R → R ≤ rPlus →
      proximityMean (fun z => iteratedDeriv k h z / h z) r ≤
        C * (Real.log (2 + proximityMean h R + Real.posLog (1 / τ)) +
          Real.log (1 / (R - r)))

/-- `lem:poisson-mean`. Boundary zeros are permitted. OPEN. -/
def PoissonMeanEstimate : Prop :=
  ∀ (H : ℂ → ℂ) (ρ : ℝ) (w : ℂ),
    AnalyticOnNhd ℂ H (Metric.closedBall 0 ρ) → w ∈ disk ρ → H w ≠ 0 →
    let t := ‖w‖ / ρ
    let q := (1 + t) / (1 - t)
    q * Real.log ‖H w‖ - (q ^ 2 - 1) * proximityMean H ρ ≤
      Real.circleAverage (fun z => Real.log ‖H z‖) 0 ρ

/-- Valid exponents from `prop:wronskian` at a = 1/4 and b = 1/2. -/
def WronskianExponents (K : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ K m ∧
    ∃ c : ℝ, 0 < c ∧ ∀ g : Fin m → ℂ → ℂ,
      (∀ j, DifferentiableOn ℂ (g j) (disk 1)) →
      (∀ j z, z ∈ disk 1 → ‖g j z‖ ≤ 1) →
      c * (leastCombinationNorm g (1 / 4)) ^ (K m) ≤
        diskSupNorm (wronskian g) (1 / 2)

/-- Full `thm:absorption` target with the manuscript's recursive radii.
The required exponents are produced as part of the conclusion. OPEN. -/
def ExplicitAbsorptionTheorem : Prop :=
  ∃ K : ℕ → ℝ, WronskianExponents K ∧
    ∀ m : ℕ, 1 ≤ m → AbsorptionAt m (disk (absorptionRadius K m))

end ModifiedCartan
