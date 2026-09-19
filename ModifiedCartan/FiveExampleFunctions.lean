import ModifiedCartan.DiskDiameter
import Mathlib.Analysis.Complex.SqrtDeriv

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

def fivePhi (z : ℂ) : ℂ := 2 * z / Complex.sqrt (1 - z ^ 4)

def fiveL (z : ℂ) : ℂ := (1 - z ^ 2) / (1 + z ^ 2) - (1 - z) / (2 * (1 + z))

theorem disk_one_sub_pow_re_pos {z : ℂ} (hz : z ∈ disk 1) {k : ℕ} (hk : k ≠ 0) :
    0 < (1 - z ^ k).re := by
  have hzn : ‖z‖ < 1 := by simpa [disk] using hz
  have hpow : ‖z ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hzn hk
  have hre := (Complex.re_le_norm (z ^ k)).trans_lt hpow
  simpa only [sub_re, one_re, sub_pos] using hre

theorem disk_one_add_pow_ne_zero {z : ℂ} (hz : z ∈ disk 1) {k : ℕ} (hk : k ≠ 0) :
    1 + z ^ k ≠ 0 := by
  have hzn : ‖z‖ < 1 := by simpa [disk] using hz
  have hpow : ‖z ^ k‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg z) hzn hk
  intro he
  have hh : z ^ k = -1 := by linear_combination he
  rw [hh] at hpow
  norm_num at hpow

theorem complex_sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  exact Complex.cpow_ofNat_inv_pow z 2

theorem fivePhi_differentiable : DifferentiableOn ℂ fivePhi (disk 1) := by
  intro z hz
  have hpos := disk_one_sub_pow_re_pos hz (by norm_num : (4 : ℕ) ≠ 0)
  have hn : 1 - z ^ 4 ≠ 0 := by intro h; simp [h] at hpos
  have hs : Complex.sqrt (1 - z ^ 4) ≠ 0 := by
    intro h
    have hh := complex_sqrt_sq (1 - z ^ 4)
    rw [h, zero_pow (by norm_num)] at hh
    exact hn hh.symm
  apply DifferentiableAt.differentiableWithinAt
  have hnum : DifferentiableAt ℂ (fun w : ℂ => 2 * w) z := by fun_prop
  have hroot : DifferentiableAt ℂ Complex.sqrt (1 - z ^ 4) :=
    Complex.differentiableAt_sqrt (Complex.mem_slitPlane_iff.mpr (Or.inl hpos))
  have hpoly : DifferentiableAt ℂ (fun w : ℂ => 1 - w ^ 4) z := by fun_prop
  have hds : DifferentiableAt ℂ (fun w : ℂ => Complex.sqrt (1 - w ^ 4)) z := by
    convert! hroot.comp z hpoly using 1
  exact hnum.div hds hs

theorem fiveL_differentiable : DifferentiableOn ℂ fiveL (disk 1) := by
  intro z hz
  have h1 : 1 + z ≠ 0 := by simpa using disk_one_add_pow_ne_zero hz (by norm_num : (1 : ℕ) ≠ 0)
  have h2 := disk_one_add_pow_ne_zero hz (by norm_num : (2 : ℕ) ≠ 0)
  apply DifferentiableAt.differentiableWithinAt
  change DifferentiableAt ℂ (fun w => (1 - w ^ 2) / (1 + w ^ 2) - (1 - w) / (2 * (1 + w))) z
  apply DifferentiableAt.sub
  · exact DifferentiableAt.div (by fun_prop) (by fun_prop) h2
  · exact DifferentiableAt.div (by fun_prop) (by fun_prop) (mul_ne_zero (by norm_num) h1)

theorem fivePhi_sq (z : ℂ) : fivePhi z ^ 2 = 4 * z ^ 2 / (1 - z ^ 4) := by
  rw [fivePhi, div_pow, complex_sqrt_sq]
  congr 1
  ring

theorem fivePhi_odd (z : ℂ) : fivePhi (-z) = -fivePhi z := by
  have hh : (-z) ^ 4 = z ^ 4 := by ring
  simp [fivePhi, hh, neg_div]

theorem fivePhi_zero : fivePhi 0 = 0 := by simp [fivePhi]

theorem fiveL_zero : fiveL 0 = 1 / 2 := by norm_num [fiveL]

theorem five_majorant_identity {z : ℂ} (hz : z ∈ disk 1) :
    fiveL z + fivePhi z ^ 2 = (1 + z) / (2 * (1 - z)) := by
  have h1p : 1 + z ≠ 0 := by simpa using disk_one_add_pow_ne_zero hz (by norm_num : (1 : ℕ) ≠ 0)
  have h1m : 1 - z ≠ 0 := by
    have hh := disk_one_sub_pow_re_pos hz (by norm_num : (1 : ℕ) ≠ 0)
    simp only [pow_one] at hh
    intro he
    simp [he] at hh
  have h2 := disk_one_add_pow_ne_zero hz (by norm_num : (2 : ℕ) ≠ 0)
  have h4 : 1 - z ^ 4 ≠ 0 :=
    ne_of_apply_ne Complex.re (ne_of_gt (disk_one_sub_pow_re_pos hz (by norm_num : (4 : ℕ) ≠ 0)))
  rw [fivePhi_sq, fiveL]
  field_simp
  ring

theorem fiveL_negative_real {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    fiveL ((-t : ℝ) : ℂ) =
      (((1 + t) * (1 - 4 * t + t ^ 2) / (2 * (1 - t) * (1 + t ^ 2)) : ℝ) : ℂ) := by
  have h1 : (1 : ℂ) - (t : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - t ≠ 0 by linarith)
  have h2 : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) + t ^ 2 ≠ 0 by positivity)
  unfold fiveL
  push_cast
  simp only [neg_sq, sub_neg_eq_add, ← sub_eq_add_neg]
  field_simp [h1, h2]
  ring

theorem fiveL_negative_iff {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (fiveL ((-t : ℝ) : ℂ)).re < 0 ↔ sharpRadius < t := by
  rw [fiveL_negative_real ht0 ht1, Complex.ofReal_re]
  have hd : 0 < 2 * (1 - t) * (1 + t ^ 2) := by positivity
  rw [div_neg_iff]
  simp only [not_lt_of_ge hd.le, and_false, hd, and_true, false_or]
  rw [mul_neg_iff]
  simp only [show 0 < 1 + t by linarith,
    not_lt_of_ge (show 0 ≤ 1 + t by linarith), true_and, false_and, or_false]
  have he : 1 - 4 * t + t ^ 2 = (t - sharpRadius) * (t + sharpRadius - 4) := by
    nlinarith [sharpRadius_quadratic]
  have hneg : t + sharpRadius - 4 < 0 := by linarith [sharpRadius_lt_one]
  rw [he, mul_neg_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨sub_pos.mpr h, hneg⟩

end ModifiedCartan
