import ModifiedCartan.CartanCircle
import ModifiedCartan.CombinationNorm

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

/-- Cartan's circle lemma transported by a dilation and a scalar normalization. -/
theorem cartan_circle_scaled {a b c S : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcS : c < S) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (H : ℂ → ℂ) (M t : ℝ),
      DifferentiableOn ℂ H (disk S) → (∀ z ∈ disk S, ‖H z‖ ≤ M) →
      0 < M → 0 < t → t ≤ diskSupNorm H a →
      ∃ ρ : ℝ, b < ρ ∧ ρ < c ∧ ∀ z : ℂ, ‖z‖ = ρ → M * (t / M) ^ γ ≤ ‖H z‖ := by
  have hS : 0 < S := ha.trans (hab.trans (hbc.trans hcS))
  have haS : a < S := hab.trans (hbc.trans hcS)
  have hcs : c / S < 1 := (div_lt_one hS).mpr hcS
  let T := (c / S + 1) / 2
  let R := (T + 1) / 2
  obtain ⟨γ, hγ, hbase⟩ := cartan_circle_at_point (div_pos ha hS)
    ((div_lt_div_iff_of_pos_right hS).mpr hab) ((div_lt_div_iff_of_pos_right hS).mpr hbc)
    (show c / S < T by dsimp [T]; linarith)
    (show T < R by dsimp [R, T]; linarith)
    (show R < 1 by dsimp [R, T]; linarith)
  refine ⟨γ, hγ, ?_⟩
  intro H M t hH hbound hM ht htmax
  have hSc : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hSnorm : ‖(S : ℂ)‖ = S := by simp [Real.norm_eq_abs, abs_of_pos hS]
  have hMnorm : ‖(M : ℂ)‖ = M := by simp [Real.norm_eq_abs, abs_of_pos hM]
  let F : ℂ → ℂ := fun z => H ((S : ℂ) * z) / (M : ℂ)
  have hmap : ∀ z ∈ disk 1, (S : ℂ) * z ∈ disk S := by
    intro z hz
    have hn : ‖z‖ < 1 := by simpa [disk] using hz
    simpa [disk, norm_mul, hSnorm, abs_of_pos hS] using (mul_lt_mul_of_pos_left hn hS)
  have hF : DifferentiableOn ℂ F (disk 1) := by
    intro z hz
    exact (((hH ((S : ℂ) * z) (hmap z hz)).differentiableAt
      (isOpen_ball.mem_nhds (hmap z hz))).comp z
      (differentiableAt_id.const_mul (S : ℂ))).div_const (M : ℂ) |>.differentiableWithinAt
  have hFbound : ∀ z ∈ disk 1, ‖F z‖ ≤ 1 := by
    intro z hz
    simpa [F, norm_div, hMnorm, abs_of_pos hM] using (div_le_one hM).mpr (hbound _ (hmap z hz))
  obtain ⟨w, hw, hwmax⟩ := diskSupNorm_attained ha.le
    (hH.continuousOn.mono (closedBall_subset_ball haS))
  have hwNorm : ‖w‖ ≤ a := by simpa using hw
  have hwS : w ∈ disk S := closedBall_subset_ball haS hw
  have htM : t ≤ M := (htmax.trans_eq hwmax).trans (hbound w hwS)
  have hwscaled : ‖w / (S : ℂ)‖ ≤ a / S := by
    simpa [norm_div, hSnorm, abs_of_pos hS] using (div_le_div_of_nonneg_right hwNorm hS.le)
  have hFw : t / M ≤ ‖F (w / (S : ℂ))‖ := by
    simpa [F, mul_div_cancel₀ _ hSc, norm_div, hMnorm, abs_of_pos hM] using
      div_le_div_of_nonneg_right (htmax.trans_eq hwmax) hM.le
  obtain ⟨r, hbr, hrc, hrbound⟩ := hbase F (t / M) (w / (S : ℂ)) hF hFbound
    (div_pos ht hM) ((div_le_one hM).mpr htM) hwscaled hFw
  refine ⟨S * r, ?_, ?_, ?_⟩
  · exact (div_lt_iff₀ hS).mp hbr |>.trans_eq (mul_comm r S)
  · simpa only [mul_comm] using (lt_div_iff₀ hS).mp hrc
  · intro z hz
    have hzr : ‖z / (S : ℂ)‖ = r := by
      rw [norm_div, hSnorm, hz]
      field_simp
    have he := hrbound (z / (S : ℂ)) hzr
    have he' : (t / M) ^ γ ≤ ‖H z‖ / M := by
      simpa [F, mul_div_cancel₀ _ hSc, norm_div, hMnorm, abs_of_pos hM] using he
    simpa only [mul_comm] using (le_div_iff₀ hM).mp he'

end ModifiedCartan
