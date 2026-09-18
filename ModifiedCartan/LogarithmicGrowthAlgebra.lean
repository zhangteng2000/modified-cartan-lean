import ModifiedCartan.PoleMoments

noncomputable section
set_option autoImplicit false
open Real
namespace ModifiedCartan

theorem rpow_le_one_add {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    x ^ p ≤ 1 + x := by
  by_cases h : x ≤ 1
  · exact (Real.rpow_le_one hx h hp).trans (by linarith)
  · exact (Real.rpow_le_self_of_one_le (le_of_not_ge h) hp1).trans (by linarith)

/-- Polynomial growth in the inverse radius gap becomes the required logarithmic error. -/
theorem log_polynomial_growth_bound {K : ℝ} (hK : 1 ≤ K) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b t : ℝ, 2 ≤ b → 1 ≤ t →
      Real.log (K * b * t ^ q) ≤ C * (Real.log b + Real.log t) := by
  let C := Real.log K / Real.log 2 + 1 + (q : ℝ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro b t hb ht
  have hb0 : 0 < b := by linarith
  have ht0 : 0 < t := by linarith
  have hlb : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hconst : Real.log K ≤ (Real.log K / Real.log 2) * Real.log b := by
    calc
      _ = (Real.log K / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlb (div_nonneg hlogK hlog2.le)
  rw [Real.log_mul (mul_pos (by linarith) hb0).ne' (pow_pos ht0 q).ne',
    Real.log_mul (by linarith : K ≠ 0) hb0.ne', Real.log_pow]
  dsimp [C]
  have hdiv : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  nlinarith [mul_nonneg hdiv hlt, mul_nonneg (Nat.cast_nonneg q) (hlog2.le.trans hlb)]

theorem log_fractional_moment_growth {A B C p : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hp : 0 < p) (hp1 : p ≤ 1) (q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D N b t : ℝ,
      0 ≤ D → 0 ≤ N → 2 ≤ b → 1 ≤ t →
      D ≤ A * (b * t ^ q) → N ≤ B * (b * t ^ q) →
      (1 / p) * Real.log (1 + D ^ p + C * N) ≤
        K * (Real.log b + Real.log t) := by
  have hABC : 1 ≤ 2 + A + C * B := by nlinarith [mul_nonneg hC hB]
  obtain ⟨K, hK, hbound⟩ := log_polynomial_growth_bound hABC q
  refine ⟨(1 / p) * K, mul_nonneg (by positivity) hK, ?_⟩
  intro D N b t hD hN hb ht hDA hNB
  have hX : 1 ≤ b * t ^ q := by
    have htq : 1 ≤ t ^ q := one_le_pow₀ ht
    nlinarith
  have hraw : 1 + D ^ p + C * N ≤ (2 + A + C * B) * b * t ^ q := by
    have hpow := rpow_le_one_add hD hp.le hp1
    have hmul := mul_le_mul_of_nonneg_left hNB hC
    nlinarith
  have hpos : 0 < 1 + D ^ p + C * N := by positivity
  have hlog := (Real.log_le_log hpos hraw).trans (hbound b t hb ht)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 1 / p)

end ModifiedCartan
