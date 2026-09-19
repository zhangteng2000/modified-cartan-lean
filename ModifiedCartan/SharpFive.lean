import ModifiedCartan.CartanFive
import ModifiedCartan.FiveOptimalityUpper
import ModifiedCartan.AbsorptionTheorem

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- The manuscript's sharp five-function theorem, including disconnected
open sets and the non-strict hyperbolic diameter endpoint. -/
theorem sharpFiveTheorem_proved : SharpFiveTheorem := by
  intro U _ hU hsub hdiam f hf hs
  obtain ⟨φ,hφ,hc⟩ := cartanExtraction_five f hf hs
  obtain ⟨ψ,hψ,hP⟩ := five_partition_from_cartan_alternative
    (unitFamily_subsequence hf φ) (zeroSum_subsequence hs φ) hc hU hsub hdiam
  exact ⟨φ ∘ ψ,hφ.comp hψ,hP⟩

theorem partition_five_at_sharpRadius : PartitionProperty 5 (disk sharpRadius) :=
  sharpFiveTheorem_proved (disk sharpRadius) ⟨0,mem_ball_self sharpRadius_pos⟩ isOpen_ball
    (ball_subset_ball sharpRadius_lt_one.le) sharpRadius_hyperbolicDiameter

theorem sharpRadius_le_optimalFiveRadius : sharpRadius ≤ optimalRadius 5 := by
  apply le_csSup (show BddAbove {r : ℝ | 0 < r ∧ r < 1 ∧ PartitionProperty 5 (disk r)} from
    ⟨1,fun r hr => hr.2.1.le⟩)
  exact ⟨sharpRadius_pos,sharpRadius_lt_one,partition_five_at_sharpRadius⟩

/-- Equality for the actual partition-property supremum, using the genuine
Gaussian counterexample for the upper bound. -/
theorem optimalFiveRadius_proved : OptimalFiveRadius :=
  le_antisymm optimalFiveRadius_le_sharpRadius sharpRadius_le_optimalFiveRadius

end ModifiedCartan
