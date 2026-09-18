import ModifiedCartan.DiskAutomorphisms
import ModifiedCartan.HarmonicComposition
import ModifiedCartan.HarmonicKernel

noncomputable section
set_option autoImplicit false
open Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

theorem harmonic_harnack_two_points {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (disk 1)) (hpos : ∀ z ∈ disk 1, 0 ≤ u z)
    {a z : ℂ} (ha : a ∈ disk 1) (hz : z ∈ disk 1) :
    (1 - ‖diskAutomorphism a z‖) / (1 + ‖diskAutomorphism a z‖) * u a ≤ u z := by
  have han : ‖a‖ < 1 := by simpa [disk] using ha
  have hcomp := harmonic_comp_analytic_to_ball hu isOpen_ball
    ((diskAutomorphism_analytic han).mono ball_subset_closedBall)
    (fun w hw => diskAutomorphism_mem_disk han hw)
  have h := (harmonic_harnack_open hcomp (fun w hw => hpos _ (diskAutomorphism_mem_disk han hw))
    (diskAutomorphism_mem_disk han hz)).1
  simpa only [sub_zero, diskAutomorphism_zero, diskAutomorphism_involutive han hz] using h

theorem diskAutomorphism_real_norm (a s : ℝ) :
    ‖diskAutomorphism (a : ℂ) (s : ℂ)‖ = |a - s| / |1 - a * s| := by
  simp only [diskAutomorphism, conj_ofReal, ← ofReal_mul, ← ofReal_one, ← ofReal_sub,
    ← ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_div]

theorem twoPoint_coefficients {t s : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hs : |s| ≤ t) :
    0 ≤ twoPointMinus t s ∧ twoPointMinus t s ≤ 1 ∧
    0 ≤ twoPointPlus t s ∧ twoPointPlus t s ≤ 1 ∧
    twoPointMinus t s = (1 - ‖diskAutomorphism ((-t : ℝ) : ℂ) (s : ℂ)‖) /
      (1 + ‖diskAutomorphism ((-t : ℝ) : ℂ) (s : ℂ)‖) ∧
    twoPointPlus t s = (1 - ‖diskAutomorphism (t : ℂ) (s : ℂ)‖) /
      (1 + ‖diskAutomorphism (t : ℂ) (s : ℂ)‖) := by
  have hst := abs_le.mp hs
  have hsp : 0 < 1 + s := by linarith
  have hsm : 0 < 1 - s := by linarith
  have htp : 0 < 1 + t := by linarith
  have htm : 0 < 1 - t := by linarith
  have hminus : 0 ≤ twoPointMinus t s := div_nonneg (mul_nonneg htm.le hsm.le) (mul_nonneg htp.le hsp.le)
  have hplus : 0 ≤ twoPointPlus t s := div_nonneg (mul_nonneg htm.le hsp.le) (mul_nonneg htp.le hsm.le)
  refine ⟨hminus, ?_, hplus, ?_, ?_, ?_⟩
  · apply (div_le_one (mul_pos htp hsp)).mpr
    nlinarith
  · apply (div_le_one (mul_pos htp hsm)).mpr
    nlinarith
  · have hts : 0 < 1 + t * s := by nlinarith [mul_nonneg ht (by linarith : 0 ≤ s + t)]
    have hnum : -t - s ≤ 0 := by linarith
    rw [diskAutomorphism_real_norm, abs_of_nonpos hnum]
    simp only [neg_mul, sub_neg_eq_add, neg_sub]
    rw [abs_of_pos hts]
    unfold twoPointMinus
    have he1 : 1 - (s + t) / (1 + t * s) = ((1 - t) * (1 - s)) / (1 + t * s) := by
      apply (eq_div_iff hts.ne').mpr
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hts.ne']
      ring
    have he2 : 1 + (s + t) / (1 + t * s) = ((1 + t) * (1 + s)) / (1 + t * s) := by
      apply (eq_div_iff hts.ne').mpr
      rw [add_mul, one_mul, div_mul_cancel₀ _ hts.ne']
      ring
    rw [he1, he2, div_div_div_cancel_right₀ hts.ne']
  · have hts : 0 < 1 - t * s := by nlinarith [mul_nonneg ht (by linarith : 0 ≤ t - s)]
    rw [diskAutomorphism_real_norm, abs_of_nonneg (by linarith : 0 ≤ t - s), abs_of_pos hts]
    unfold twoPointPlus
    have he1 : 1 - (t - s) / (1 - t * s) = ((1 - t) * (1 + s)) / (1 - t * s) := by
      apply (eq_div_iff hts.ne').mpr
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hts.ne']
      ring
    have he2 : 1 + (t - s) / (1 - t * s) = ((1 + t) * (1 - s)) / (1 - t * s) := by
      apply (eq_div_iff hts.ne').mpr
      rw [add_mul, one_mul, div_mul_cancel₀ _ hts.ne']
      ring
    rw [he1, he2, div_div_div_cancel_right₀ hts.ne']

/-- The full two-harmonic-function comparison on normalized real geodesics. -/
theorem real_segment_harmonic_comparison {q : ℝ} (hq : 0 < q) (hqr : q < sharpRadius) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (U P Q : ℂ → ℝ) (t C₀ : ℝ),
      HarmonicOnNhd U (disk 1) → HarmonicOnNhd P (disk 1) → HarmonicOnNhd Q (disk 1) →
      (∀ z ∈ disk 1, 0 < U z) → (∀ z ∈ disk 1, 0 ≤ P z) → (∀ z ∈ disk 1, 0 ≤ Q z) →
      0 ≤ t → t ≤ q → 0 ≤ C₀ →
      U ((-t : ℝ) : ℂ) - C₀ ≤ Q ((-t : ℝ) : ℂ) → U (t : ℂ) - C₀ ≤ P (t : ℂ) →
      ∀ s : ℝ, |s| ≤ t → U (s : ℂ) - P (s : ℂ) - Q (s : ℂ) ≤ -ε * U (s : ℂ) + 2 * C₀ := by
  obtain ⟨ε, hε, htwo⟩ := two_point_harmonic hq hqr
  refine ⟨ε, hε, ?_⟩
  intro U P Q t C₀ hU hP hQ hUpos hPpos hQpos ht htq hC hQend hPend s hs
  have ht1 : t < 1 := htq.trans_lt (hqr.trans sharpRadius_lt_one)
  have htn : (t : ℂ) ∈ disk 1 := by simpa [disk, abs_of_nonneg ht] using ht1
  have hntn : ((-t : ℝ) : ℂ) ∈ disk 1 := by simpa [disk, abs_of_nonneg ht] using ht1
  have hsn : (s : ℂ) ∈ disk 1 := by simpa [disk] using hs.trans_lt ht1
  obtain ⟨hkm0, hkm1, hkp0, hkp1, hkm, hkp⟩ := twoPoint_coefficients ht ht1 hs
  have hQbound := harmonic_harnack_two_points hQ hQpos hntn hsn
  have hPbound := harmonic_harnack_two_points hP hPpos htn hsn
  rw [← hkm] at hQbound
  rw [← hkp] at hPbound
  have hQmul := mul_le_mul_of_nonneg_left hQend hkm0
  have hPmul := mul_le_mul_of_nonneg_left hPend hkp0
  have hkmC := mul_le_mul_of_nonneg_right hkm1 hC
  have hkpC := mul_le_mul_of_nonneg_right hkp1 hC
  have hUU := htwo U hU hUpos t s ht htq hs
  nlinarith

end ModifiedCartan
