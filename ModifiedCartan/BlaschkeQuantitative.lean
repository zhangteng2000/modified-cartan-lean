import ModifiedCartan.Blaschke

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
namespace ModifiedCartan

def blaschkeDecayConstant (r₀ α : ℝ) : ℝ := r₀ * (r₀ ^ 2 - α ^ 2) / 8

theorem blaschkeDecayConstant_pos {r₀ α : ℝ} (hα : 0 ≤ α) (hαr : α < r₀) :
    0 < blaschkeDecayConstant r₀ α := by
  have hr : 0 < r₀ := hα.trans_lt hαr
  unfold blaschkeDecayConstant
  apply div_pos (mul_pos hr _) (by norm_num)
  nlinarith

/-- A quantitative version of the strict Blaschke contraction, uniform as the
zero approaches the outer circle at a prescribed distance d. -/
theorem blaschkeFactor_exponential_bound {r₀ α S T d : ℝ} {a w : ℂ}
    (hα : 0 ≤ α) (hαr : α < r₀) (hrS : r₀ ≤ S) (hS1 : S ≤ 1)
    (hd : 0 < d) (hTd : T + d ≤ S) (ha : ‖a‖ ≤ T) (hw : ‖w‖ ≤ α) :
    ‖blaschkeFactor S a w‖ ≤ Real.exp (-(blaschkeDecayConstant r₀ α * d)) := by
  have hr : 0 < r₀ := hα.trans_lt hαr
  have hS : 0 < S := hr.trans_le hrS
  have haS : ‖a‖ < S := by linarith
  have hwS : ‖w‖ < S := hw.trans_lt (hαr.trans_le hrS)
  let x := ‖blaschkeFactor S a w‖
  let D := ‖((S ^ 2 : ℝ) : ℂ) - conj a * w‖
  have hx : 0 ≤ x := norm_nonneg _
  have hx1 : x ≤ 1 := blaschkeFactor_norm_le_one hS haS hwS.le
  have hD : 0 ≤ D := norm_nonneg _
  have hDne : D ≠ 0 := norm_ne_zero_iff.mpr (blaschke_numerator_ne_zero hS haS hwS.le)
  have hD2 : D ≤ 2 := by
    calc
      _ ≤ ‖((S ^ 2 : ℝ) : ℂ)‖ + ‖conj a * w‖ := norm_sub_le _ _
      _ = S ^ 2 + ‖a‖ * ‖w‖ := by simp
      _ ≤ S ^ 2 + S ^ 2 := by
        have hh := mul_le_mul haS.le hwS.le (norm_nonneg _) hS.le
        nlinarith
      _ ≤ 2 := by nlinarith
  have he : x * D = S * ‖w - a‖ := by
    dsimp [x, D]
    simp only [blaschkeFactor, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
    exact div_mul_cancel₀ _ hDne
  have hid := blaschke_norm_identity S a w
  change D ^ 2 - S ^ 2 * ‖w - a‖ ^ 2 = (S ^ 2 - ‖a‖ ^ 2) * (S ^ 2 - ‖w‖ ^ 2) at hid
  have hid' : (1 - x ^ 2) * D ^ 2 = (S ^ 2 - ‖a‖ ^ 2) * (S ^ 2 - ‖w‖ ^ 2) := by
    have hesq := congrArg (fun t : ℝ => t ^ 2) he
    nlinarith only [hid, hesq]
  have hfirst : r₀ * d ≤ S ^ 2 - ‖a‖ ^ 2 := by
    have hgap : d ≤ S - ‖a‖ := by linarith
    have hh := mul_le_mul hgap (show r₀ ≤ S + ‖a‖ by linarith [norm_nonneg a]) hr.le (by linarith : 0 ≤ S - ‖a‖)
    nlinarith only [hh]
  have hsecond : r₀ ^ 2 - α ^ 2 ≤ S ^ 2 - ‖w‖ ^ 2 := by
    nlinarith [norm_nonneg w]
  have hsmall : 0 ≤ r₀ ^ 2 - α ^ 2 := by nlinarith
  have hproduct := mul_le_mul hfirst hsecond hsmall (by nlinarith [norm_nonneg a] : 0 ≤ S ^ 2 - ‖a‖ ^ 2)
  have hupper : (1 - x ^ 2) * D ^ 2 ≤ 8 * (1 - x) := by
    have hp : 0 ≤ 1 - x ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left (show D ^ 2 ≤ 4 by nlinarith) hp
    nlinarith
  have hlinear : x ≤ 1 - blaschkeDecayConstant r₀ α * d := by
    rw [hid'] at hupper
    dsimp [blaschkeDecayConstant]
    nlinarith only [hproduct, hupper]
  exact hlinear.trans (by simpa only [neg_add_eq_sub, add_comm] using Real.add_one_le_exp (-(blaschkeDecayConstant r₀ α * d)))

end ModifiedCartan
