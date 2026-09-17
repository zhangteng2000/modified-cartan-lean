import ModifiedCartan.Basic
import ModifiedCartan.Laurent
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter Topology
open scoped ENNReal
namespace ModifiedCartan

/-- Analytic discs in a subset of C^N, with specified center and derivative.
On a smooth complex subvariety this gives the ambient-coordinate version
of the discs used to define its Kobayashi--Royden metric. -/
structure TangentDisc {N : ℕ} (Y : Set (Fin N → ℂ))
    (x v : Fin N → ℂ) (t : ℝ) where
  map : ℂ → Fin N → ℂ
  holomorphic : ∀ j, DifferentiableOn ℂ (fun z => map z j) (disk 1)
  mapsTo : ∀ z ∈ disk 1, map z ∈ Y
  center : map 0 = x
  tangent : ∀ j, HasDerivAt (fun z => map z j) ((t : ℂ) * v j) 0

/-- The value +infinity handles an empty set of admissible discs correctly. -/
def kobayashiRoyden {N : ℕ} (Y : Set (Fin N → ℂ)) (x v : Fin N → ℂ) : ℝ≥0∞ :=
  sInf {c | ∃ t : ℝ, 0 < t ∧ c = ENNReal.ofReal (1 / t) ∧ Nonempty (TangentDisc Y x v t)}

theorem kobayashiRoyden_le_of_disc {N : ℕ} {Y : Set (Fin N → ℂ)}
    {x v : Fin N → ℂ} {t : ℝ} (ht : 0 < t) (F : TangentDisc Y x v t) :
    kobayashiRoyden Y x v ≤ ENNReal.ofReal (1 / t) :=
  sInf_le ⟨t, ht, rfl, ⟨F⟩⟩

def orbitDisc {N : ℕ} {Y : Set (Fin N → ℂ)} {x v : Fin N → ℂ}
    (hx : ∀ j, x j ≠ 0) (hY : ∀ z, exponentialOrbit x v z ∈ Y) (t : ℝ) :
    TangentDisc Y x v t where
  map z := exponentialOrbit x v ((t : ℂ) * z)
  holomorphic := by intro j; unfold exponentialOrbit; fun_prop
  mapsTo := by intro z _; exact hY _
  center := by simpa only [mul_zero] using exponentialOrbit_at_zero x v
  tangent := by
    intro j
    have h := (((hasDerivAt_id (0 : ℂ)).const_mul ((v j / x j) * (t : ℂ))).cexp.const_mul (x j))
    have he : x j * ((v j / x j) * (t : ℂ)) = (t : ℂ) * v j := by
      field_simp [hx j]
    simpa [exponentialOrbit, mul_assoc, he] using h

/-- The backward implication of Theorem `thm:torus-zero`. No algebraicity or smoothness
is needed for this implication. The forward implication is still open. -/
theorem kobayashiRoyden_zero_of_orbit {N : ℕ} {Y : Set (Fin N → ℂ)}
    {x v : Fin N → ℂ} (hx : ∀ j, x j ≠ 0)
    (hY : ∀ z, exponentialOrbit x v z ∈ Y) : kobayashiRoyden Y x v = 0 := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply le_antisymm _ bot_le
  apply ge_of_tendsto' hlim
  intro n
  exact kobayashiRoyden_le_of_disc (by positivity) (orbitDisc hx hY ((n : ℝ) + 1))

end ModifiedCartan
