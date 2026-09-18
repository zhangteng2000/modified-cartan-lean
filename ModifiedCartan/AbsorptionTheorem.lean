import ModifiedCartan.SharpTwoAbsorption
import ModifiedCartan.AbsorptionInduction
import ModifiedCartan.WronskianExponents
import ModifiedCartan.HolomorphicCancellation

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Complex Metric Set
namespace ModifiedCartan

/-- The closed Euclidean disk with the manuscript's sharp radius has
pseudohyperbolic diameter at most one half. -/
theorem sharpRadius_pseudodiameter {a z : ℂ}
    (ha : ‖a‖ ≤ sharpRadius) (hz : ‖z‖ ≤ sharpRadius) :
    ‖diskAutomorphism a z‖ ≤ 1 / 2 := by
  have hr := sharpRadius_pos
  have hr1 := sharpRadius_lt_one
  have har := sq_le_sq₀ (norm_nonneg a) hr.le |>.mpr ha
  have hzr := sq_le_sq₀ (norm_nonneg z) hr.le |>.mpr hz
  have hr2 : sharpRadius ^ 2 < 1 := by nlinarith
  have hnum : ‖z - a‖ ≤ 2 * sharpRadius := by
    have h := norm_sub_le z a
    linarith
  have hnum2 : ‖z - a‖ ^ 2 ≤ 4 * sharpRadius ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (z - a)) (by positivity : 0 ≤ 2 * sharpRadius)).mpr hnum
    nlinarith only [h]
  have hfactor : (1 - sharpRadius ^ 2) ^ 2 = 12 * sharpRadius ^ 2 := by
    have h := sharpRadius_quadratic
    nlinarith [sq_nonneg (sharpRadius ^ 2), congrArg (fun x : ℝ => x ^ 2) h]
  have hprod : (1 - sharpRadius ^ 2) ^ 2 ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    rw [pow_two]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by nlinarith)
  have hid := blaschke_norm_identity 1 a z
  simp only [one_pow, Complex.ofReal_one, one_mul] at hid
  have hden : 0 < ‖1 - conj a * z‖ := norm_pos_iff.mpr
    (diskAutomorphism_denominator_ne_zero (ha.trans_lt hr1) (hz.trans hr1.le))
  have hbound : 2 * ‖z - a‖ ≤ ‖1 - conj a * z‖ := by
    rw [hfactor] at hprod
    nlinarith [sq_nonneg (‖1 - conj a * z‖ - 2 * ‖z - a‖)]
  rw [diskAutomorphism, norm_div, norm_sub_rev a z]
  apply (div_le_iff₀ hden).mpr
  linarith

theorem sharpRadius_hyperbolicDiameter :
    HasHyperbolicDiameterLE (disk sharpRadius) (Real.log 3) := by
  intro z hz w hw
  have hz' : ‖z‖ < sharpRadius := by simpa [disk] using hz
  have hw' : ‖w‖ < sharpRadius := by simpa [disk] using hw
  apply (hyperbolicDistance_le_log_three_iff
    (by simpa [disk] using hz'.trans sharpRadius_lt_one)
    (by simpa [disk] using hw'.trans sharpRadius_lt_one)).mpr
  exact sharpRadius_pseudodiameter hw'.le hz'.le

theorem absorption_two : AbsorptionAt 2 (disk sharpRadius) := by
  apply sharp_two_absorption isOpen_ball _ sharpRadius_hyperbolicDiameter
  exact ball_subset_ball sharpRadius_lt_one.le

/-- The exact recursive radii, for every valid exponent sequence bounded below by m. -/
theorem absorption_at_recursive_radius {K : ℕ → ℝ} (hK : WronskianExponents K)
    (hKm : ∀ m : ℕ, (m : ℝ) ≤ K m) :
    ∀ m : ℕ, 1 ≤ m → AbsorptionAt m (disk (absorptionRadius K m))
  | 0, hm => by omega
  | 1, _ => absorption_one
  | 2, _ => absorption_two
  | n + 3, _ => by
    have hr1 : absorptionRadius K (n + 2) ≤ 1 := by
      simpa [absorptionRadius] using absorptionRadius_antitone hKm (show 0 ≤ n + 2 by omega)
    exact absorption_successor hK (by omega) (absorptionRadius_pos hKm _) hr1
      (absorption_at_recursive_radius hK hKm (n + 2) (by omega))

theorem explicitAbsorptionTheorem_proved : ExplicitAbsorptionTheorem := by
  obtain ⟨K, _hK0, _hK1, hK, hKm⟩ := exists_wronskianExponents
  exact ⟨K, hK, absorption_at_recursive_radius hK hKm⟩

theorem absorptionTheorem_proved : AbsorptionTheorem := by
  obtain ⟨K, _hK0, _hK1, hK, hKm⟩ := exists_wronskianExponents
  intro m hm
  refine ⟨absorptionRadius K m, absorptionRadius_pos hKm m, ?_,
    absorption_at_recursive_radius hK hKm m hm⟩
  simpa [absorptionRadius] using absorptionRadius_antitone hKm (show 0 ≤ m by omega)

end ModifiedCartan
