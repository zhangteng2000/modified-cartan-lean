import ModifiedCartan.Blaschke
import ModifiedCartan.Statements

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Complex Metric Set Real
namespace ModifiedCartan

def diskAutomorphism (a z : ℂ) : ℂ := (a - z) / (1 - conj a * z)

theorem diskAutomorphism_eq_blaschke (a z : ℂ) :
    diskAutomorphism a z = -blaschkeFactor 1 a z := by
  simp only [diskAutomorphism, blaschkeFactor, one_pow, ofReal_one, one_mul]
  ring

theorem diskAutomorphism_denominator_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  simpa using blaschke_numerator_ne_zero (by norm_num : (0 : ℝ) < 1) ha hz

theorem diskAutomorphism_analytic {a : ℂ} (ha : ‖a‖ < 1) :
    AnalyticOnNhd ℂ (diskAutomorphism a) (closedBall (0 : ℂ) 1) := by
  have he : diskAutomorphism a = fun z => -blaschkeFactor 1 a z := funext (diskAutomorphism_eq_blaschke a)
  rw [he]
  exact (blaschkeFactor_analytic (by norm_num) ha).neg

theorem diskAutomorphism_mem_disk {a z : ℂ} (ha : ‖a‖ < 1) (hz : z ∈ disk 1) :
    diskAutomorphism a z ∈ disk 1 := by
  have hn : ‖z‖ < 1 := by simpa [disk] using hz
  have hh := blaschkeFactor_norm_lt_one (by norm_num) ha hn
  simpa only [disk, mem_ball, dist_zero_right, diskAutomorphism_eq_blaschke, norm_neg] using hh

theorem diskAutomorphism_involutive {a z : ℂ} (ha : ‖a‖ < 1) (hz : z ∈ disk 1) :
    diskAutomorphism a (diskAutomorphism a z) = z := by
  have hden := diskAutomorphism_denominator_ne_zero ha (by simpa [disk] using (mem_ball.mp hz).le)
  have himage := diskAutomorphism_mem_disk ha hz
  have hden' := diskAutomorphism_denominator_ne_zero ha
    (show ‖diskAutomorphism a z‖ ≤ 1 by exact le_of_lt (by simpa [disk] using himage))
  unfold diskAutomorphism at *
  apply (div_eq_iff hden').mpr
  apply (mul_right_cancel₀ hden)
  have hx := div_mul_cancel₀ (a - z) hden
  linear_combination -(1 - conj a * z) * hx

theorem diskAutomorphism_zero (a : ℂ) : diskAutomorphism a 0 = a := by simp [diskAutomorphism]

theorem diskAutomorphism_self (a : ℂ) : diskAutomorphism a a = 0 := by simp [diskAutomorphism]

theorem diskAutomorphism_maps_onto {a : ℂ} (ha : ‖a‖ < 1) :
    diskAutomorphism a '' disk 1 = disk 1 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact diskAutomorphism_mem_disk ha hw
  · intro hz
    exact ⟨diskAutomorphism a z, diskAutomorphism_mem_disk ha hz, diskAutomorphism_involutive ha hz⟩

theorem diskAutomorphism_hasDerivAt {a z : ℂ} (ha : ‖a‖ < 1) (hz : z ∈ disk 1) :
    HasDerivAt (diskAutomorphism a) ((conj a * a - 1) / (1 - conj a * z) ^ 2) z := by
  have hden := diskAutomorphism_denominator_ne_zero ha
    (show ‖z‖ ≤ 1 by exact le_of_lt (by simpa [disk] using hz))
  have hd := ((hasDerivAt_const z a).sub (hasDerivAt_id z)).div
    ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (conj a))) hden
  simp only [Pi.sub_def, Pi.div_def, id_eq, zero_sub, mul_one] at hd
  have he : (-1 * (1 - conj a * z) - (a - z) * -conj a) /
      (1 - conj a * z) ^ 2 = (conj a * a - 1) / (1 - conj a * z) ^ 2 := by ring
  rw [he] at hd
  exact hd

theorem hyperbolicDistance_eq_automorphism (z w : ℂ) :
    hyperbolicDistance z w =
      Real.log ((1 + ‖diskAutomorphism w z‖) / (1 - ‖diskAutomorphism w z‖)) := by
  unfold hyperbolicDistance diskAutomorphism
  rw [norm_div, norm_div, norm_sub_rev w z]
  rfl

theorem hyperbolicDistance_self (z : ℂ) : hyperbolicDistance z z = 0 := by
  simp [hyperbolicDistance]

theorem hyperbolicDistance_nonneg {z w : ℂ} (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    0 ≤ hyperbolicDistance z w := by
  rw [hyperbolicDistance_eq_automorphism]
  have hwa : ‖w‖ < 1 := by simpa [disk] using hw
  have hnorm : ‖diskAutomorphism w z‖ < 1 := by simpa [disk] using diskAutomorphism_mem_disk hwa hz
  apply Real.log_nonneg
  apply (le_div_iff₀ (by linarith : 0 < 1 - ‖diskAutomorphism w z‖)).mpr
  linarith [norm_nonneg (diskAutomorphism w z)]

theorem hyperbolicDistance_symm (z w : ℂ) : hyperbolicDistance z w = hyperbolicDistance w z := by
  have he : ‖1 - conj w * z‖ = ‖1 - conj z * w‖ := by
    calc
      _ = ‖conj (1 - conj w * z)‖ := (norm_conj _).symm
      _ = _ := by simp [mul_comm]
  unfold hyperbolicDistance
  simp only [star_def, norm_div]
  rw [he, norm_sub_rev z w]

end ModifiedCartan
