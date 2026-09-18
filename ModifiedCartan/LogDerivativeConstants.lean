import ModifiedCartan.LocalLogDerivativePoles

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

def logDerivativeRegularBound (n : ℕ) (α r R E N : ℝ) : ℝ :=
  let S := (r + R) / 2
  let T := (3 * r + R) / 4
  N * ((n.factorial : ℝ) * (2 / (S - r)) / ((S - r) / 2) ^ n) +
    ((n + 1).factorial : ℝ) / ((T - r) / 2) ^ (n + 1) *
      (2 * ((1 + (T + α) / (T - α)) * E) * ((T + r) / 2) / (T - (T + r) / 2))

theorem logDerivativeRegularBound_nonneg {n : ℕ} {α r R E N : ℝ}
    (hα : 0 ≤ α) (hαr : α < r) (hrR : r < R) (hE : 0 ≤ E) (hN : 0 ≤ N) :
    0 ≤ logDerivativeRegularBound n α r R E N := by
  unfold logDerivativeRegularBound
  have hS : 0 < (r + R) / 2 - r := by linarith
  have hT : 0 < (3 * r + R) / 4 - r := by linarith
  have hTα : 0 < (3 * r + R) / 4 - α := by linarith
  have hmid : 0 < (3 * r + R) / 4 - ((3 * r + R) / 4 + r) / 2 := by linarith
  have hnum : 0 ≤ (3 * r + R) / 4 + α := by linarith
  have hnum' : 0 ≤ (3 * r + R) / 4 + r := by linarith
  positivity

theorem logDerivativeRegularBound_polynomial {α r₀ : ℝ}
    (hα : 0 < α) (hαr : α < r₀) (n : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ r R b E N : ℝ,
      r₀ ≤ r → r < R → R < 1 → 2 ≤ b → 0 ≤ E →
      E ≤ 4 * b * (1 / (R - r)) → 0 ≤ N →
      N ≤ E / (blaschkeDecayConstant r₀ α * ((R - r) / 4)) →
      N ≤ B * (b * (1 / (R - r)) ^ (n + 3)) ∧
      logDerivativeRegularBound n α r R E N ≤ A * (b * (1 / (R - r)) ^ (n + 3)) := by
  let c := blaschkeDecayConstant r₀ α
  let Q := 1 + (1 + α) / (r₀ - α)
  let B := 16 / c
  let A := B * (n.factorial : ℝ) * 4 ^ (n + 1) +
    64 * ((n + 1).factorial : ℝ) * 8 ^ (n + 1) * Q
  have hc : 0 < c := blaschkeDecayConstant_pos hα.le hαr
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
  intro r R b E N hr₀ hrR hR hb hE hEb hN hNb
  let t := 1 / (R - r)
  let T := (3 * r + R) / 4
  have hr : 0 < r := hα.trans (hαr.trans_le hr₀)
  have hg : 0 < R - r := sub_pos.mpr hrR
  have ht : 1 ≤ t := (le_div_iff₀ hg).mpr (by linarith)
  have ht0 : 0 < t := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hT : r < T := by dsimp [T]; linarith
  have hT1 : T ≤ 1 := by dsimp [T]; linarith
  have hQb : 1 + (T + α) / (T - α) ≤ Q := by
    dsimp [Q]
    apply add_le_add le_rfl
    apply (div_le_div_iff₀ (by linarith : 0 < T - α) (sub_pos.mpr hαr)).mpr
    nlinarith
  have hTb : (T + r) / 2 ≤ 1 := by linarith
  have hTmid : 0 ≤ (T + r) / 2 := by linarith
  have hNN : N ≤ B * b * t ^ 2 := by
    calc
      N ≤ E / (c * ((R - r) / 4)) := hNb
      _ = (4 / c) * E * t := by dsimp [t]; field_simp
      _ ≤ (4 / c) * (4 * b * t) * t := by gcongr
      _ = B * b * t ^ 2 := by dsimp [B]; ring
  have hNfinal : N ≤ B * (b * t ^ (n + 3)) := by
    apply hNN.trans
    have hp : t ^ 2 ≤ t ^ (n + 3) := pow_le_pow_right₀ ht (by omega)
    nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg hB hb0)]
  refine ⟨hNfinal, ?_⟩
  have hrew : logDerivativeRegularBound n α r R E N =
      N * ((n.factorial : ℝ) * (4 * t) * (4 * t) ^ n) +
      ((n + 1).factorial : ℝ) * (8 * t) ^ (n + 1) *
        (2 * ((1 + (T + α) / (T - α)) * E) * ((T + r) / 2) * (8 * t)) := by
    have he1 : 2 / ((r + R) / 2 - r) = 4 * t := by
      rw [show (r + R) / 2 - r = (R - r) / 2 by ring]
      dsimp [t]
      field_simp
      norm_num
    have he2 : (((r + R) / 2 - r) / 2)⁻¹ = 4 * t := by
      rw [show ((r + R) / 2 - r) / 2 = (R - r) / 4 by ring]
      dsimp [t]
      field_simp
    have he3 : ((T - r) / 2)⁻¹ = 8 * t := by
      rw [show (T - r) / 2 = (R - r) / 8 by dsimp [T]; ring]
      dsimp [t]
      field_simp
    have he4 : (T - (T + r) / 2)⁻¹ = 8 * t := by
      rw [show T - (T + r) / 2 = (R - r) / 8 by dsimp [T]; ring]
      dsimp [t]
      field_simp
    unfold logDerivativeRegularBound
    change N * (_ * (2 / ((r + R) / 2 - r)) / (((r + R) / 2 - r) / 2) ^ n) +
      _ / ((T - r) / 2) ^ (n + 1) * (_ / (T - (T + r) / 2)) = _
    rw [he1, div_eq_mul_inv, ← inv_pow, he2, div_eq_mul_inv, ← inv_pow, he3,
      div_eq_mul_inv, he4]
  rw [hrew]
  have hqnonneg : 0 ≤ 1 + (T + α) / (T - α) := by
    have hnum : 0 ≤ T + α := by linarith
    have hden : 0 < T - α := by linarith
    positivity
  calc
    _ ≤ (B * b * t ^ 2) * ((n.factorial : ℝ) * (4 * t) * (4 * t) ^ n) +
      ((n + 1).factorial : ℝ) * (8 * t) ^ (n + 1) *
        (2 * (Q * (4 * b * t)) * 1 * (8 * t)) := by
      gcongr
    _ = A * (b * t ^ (n + 3)) := by
      dsimp [A]
      simp only [mul_pow, pow_add, pow_one]
      ring

end ModifiedCartan
