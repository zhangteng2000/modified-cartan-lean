import ModifiedCartan.Statements

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

theorem scaled_cartan_power {τ c M : ℝ} (hτ : 0 ≤ τ) (hc : 0 < c) (hM : 0 < M)
    (K γ : ℝ) : M * (c * τ ^ K / M) ^ γ = (M * (c / M) ^ γ) * τ ^ (K * γ) := by
  have he : c * τ ^ K / M = (c / M) * τ ^ K := by ring
  rw [he, Real.mul_rpow (div_nonneg hc.le hM.le) (Real.rpow_nonneg hτ K),
    Real.rpow_mul hτ]
  ring

theorem wronskian_power_algebra {τ Δ A d β L : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hA : 0 < A) (_hd : 0 < d)
    (hL : 2 * β + 1 ≤ L) (hbound : τ * (d * τ ^ β) ^ 2 ≤ A * Δ) :
    (d ^ 2 / A) * τ ^ L ≤ Δ := by
  have he : τ * (d * τ ^ β) ^ 2 = d ^ 2 * τ ^ (2 * β + 1) := by
    rw [Real.rpow_add hτ, Real.rpow_one, mul_comm (2 : ℝ) β,
      Real.rpow_mul hτ.le, Real.rpow_two]
    ring
  rw [he] at hbound
  have hpow := Real.rpow_le_rpow_of_exponent_ge hτ hτ1 hL
  have hle := (mul_le_mul_of_nonneg_left hpow (sq_nonneg d)).trans hbound
  calc
    _ = (d ^ 2 * τ ^ L) / A := by ring
    _ ≤ Δ := (div_le_iff₀ hA).mpr (by simpa [mul_comm] using hle)

end ModifiedCartan
