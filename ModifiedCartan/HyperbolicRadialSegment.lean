import ModifiedCartan.HyperbolicCoordinates

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

def hyperbolicSegment (a b : ℂ) : Set ℂ :=
  {z | z ∈ disk 1 ∧ hyperbolicDistance a z + hyperbolicDistance z b = hyperbolicDistance a b}

theorem hyperbolicDistance_zero_left (z : ℂ) :
    hyperbolicDistance 0 z = hyperbolicRadialCoordinate ‖z‖ := by
  rw [hyperbolicDistance_eq_automorphism, diskAutomorphism_zero]
  rfl

theorem hyperbolic_radial_addition {r u v : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hv0 : 0 ≤ v) (hv1 : v < 1)
    (h : hyperbolicRadialCoordinate u + hyperbolicRadialCoordinate v = hyperbolicRadialCoordinate r) :
    v = (r - u) / (1 - r * u) := by
  have hrm : 0 < 1 - r := by linarith
  have hum : 0 < 1 - u := by linarith
  have hvm : 0 < 1 - v := by linarith
  have hru : r * u < 1 :=
    (mul_le_mul_of_nonneg_left hu1.le hr0).trans_lt (by simpa using hr1)
  have he := congrArg Real.exp h
  simp only [hyperbolicRadialCoordinate, Real.exp_add,
    Real.exp_log (div_pos (by linarith : 0 < 1 + u) hum),
    Real.exp_log (div_pos (by linarith : 0 < 1 + v) hvm),
    Real.exp_log (div_pos (by linarith : 0 < 1 + r) hrm)] at he
  field_simp [hrm.ne', hum.ne', hvm.ne'] at he
  apply (eq_div_iff (by linarith : 1 - r * u ≠ 0)).mpr
  nlinarith [he]

theorem diskAutomorphism_real_norm_square {r : ℝ} {z : ℂ}
    (hr : |r| < 1) (hz : z ∈ disk 1) :
    ‖diskAutomorphism (r : ℂ) z‖ ^ 2 *
      (1 - 2 * r * z.re + r ^ 2 * ‖z‖ ^ 2) = r ^ 2 - 2 * r * z.re + ‖z‖ ^ 2 := by
  have hn : ‖(r : ℂ)‖ < 1 := by simpa using hr
  have hd := diskAutomorphism_denominator_ne_zero hn
    (show ‖z‖ ≤ 1 by exact le_of_lt (by simpa [disk] using hz))
  have hden : ‖1 - (r : ℂ) * z‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    simpa using hd
  have he : ‖diskAutomorphism (r : ℂ) z‖ * ‖1 - (r : ℂ) * z‖ = ‖(r : ℂ) - z‖ := by
    rw [diskAutomorphism, conj_ofReal, norm_div, div_mul_cancel₀ _ hden]
  have hd2 : ‖1 - (r : ℂ) * z‖ ^ 2 = 1 - 2 * r * z.re + r ^ 2 * ‖z‖ ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hn2 : ‖(r : ℂ) - z‖ ^ 2 = r ^ 2 - 2 * r * z.re + ‖z‖ ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h := congrArg (fun x : ℝ => x ^ 2) he
  rwa [mul_pow, hd2, hn2] at h

set_option maxHeartbeats 800000 in
/-- Equality in the hyperbolic triangle inequality along a radial segment
forces the middle point to be on that real segment. -/
theorem hyperbolic_radial_segment_rigidity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : z ∈ disk 1)
    (h : hyperbolicDistance 0 z + hyperbolicDistance z (r : ℂ) = hyperbolicDistance 0 (r : ℂ)) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ r ∧ z = (s : ℂ) := by
  let u := ‖z‖
  let v := ‖diskAutomorphism (r : ℂ) z‖
  have hu0 : 0 ≤ u := norm_nonneg _
  have hu1 : u < 1 := by simpa [u, disk] using hz
  have hr : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  have hrD : (r : ℂ) ∈ disk 1 := by simpa [disk] using hr
  have hv0 : 0 ≤ v := norm_nonneg _
  have hv1 : v < 1 := by
    simpa [v, disk] using diskAutomorphism_mem_disk (show ‖(r : ℂ)‖ < 1 by simpa using hr) hz
  have hleft : hyperbolicDistance 0 z = hyperbolicRadialCoordinate u :=
    hyperbolicDistance_zero_left z
  have hmid : hyperbolicDistance z (r : ℂ) = hyperbolicRadialCoordinate v := by
    rw [hyperbolicDistance_eq_automorphism]
    rfl
  have hright : hyperbolicDistance 0 (r : ℂ) = hyperbolicRadialCoordinate r := by
    rw [hyperbolicDistance_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have he : hyperbolicRadialCoordinate u + hyperbolicRadialCoordinate v = hyperbolicRadialCoordinate r := by
    rwa [hleft, hmid, hright] at h
  have hlv : 0 ≤ hyperbolicRadialCoordinate v := by
    have hnonneg := hyperbolicDistance_nonneg hz hrD
    rwa [hmid] at hnonneg
  have hur : u ≤ r := (hyperbolicRadialCoordinate_le_iff
    (by simpa [abs_of_nonneg hu0] using hu1) hr).mp (by linarith)
  by_cases hrz : r = 0
  · have huz : u = 0 := by linarith
    have hz0 : z = 0 := norm_eq_zero.mp huz
    exact ⟨0, le_rfl, hr0, by simpa using hz0⟩
  have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
  have hru : r * u < 1 :=
    (mul_le_mul_of_nonneg_left hu1.le hr0).trans_lt (by simpa using hr1)
  have hv := hyperbolic_radial_addition hr0 hr1 hu0 hu1 hv0 hv1 he
  have hs := diskAutomorphism_real_norm_square hr hz
  change v ^ 2 * (1 - 2 * r * z.re + r ^ 2 * u ^ 2) = r ^ 2 - 2 * r * z.re + u ^ 2 at hs
  rw [hv, div_pow, div_mul_eq_mul_div] at hs
  have hs' := (div_eq_iff (pow_ne_zero 2 (by linarith : 1 - r * u ≠ 0))).mp hs
  have hp : (2 * r * (1 - r ^ 2) * (1 - u ^ 2)) * (z.re - u) = 0 := by
    linear_combination hs'
  have hcoef : 0 < 2 * r * (1 - r ^ 2) * (1 - u ^ 2) := by
    have hr2 : 0 < 1 - r ^ 2 := by nlinarith
    have hu2 : 0 < 1 - u ^ 2 := by nlinarith
    positivity
  have hre : z.re = u := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hcoef.ne')
  have him : z.im = 0 := by
    have hh := Complex.sq_norm_sub_sq_re z
    change u ^ 2 - z.re ^ 2 = z.im ^ 2 at hh
    rw [hre] at hh
    nlinarith [sq_nonneg z.im]
  refine ⟨u, hu0, hur, ?_⟩
  exact Complex.ext (by simpa using hre) (by simpa using him)

theorem hyperbolicSegment_zero_real {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    hyperbolicSegment 0 (r : ℂ) = Complex.ofReal '' Icc (0 : ℝ) r := by
  ext z
  constructor
  · rintro ⟨hz, h⟩
    obtain ⟨s, hs0, hsr, hs⟩ := hyperbolic_radial_segment_rigidity hr0 hr1 hz h
    exact ⟨s, ⟨hs0, hsr⟩, hs.symm⟩
  · rintro ⟨s, ⟨hs0, hsr⟩, rfl⟩
    have hs : |s| < 1 := by rw [abs_of_nonneg hs0]; exact hsr.trans_lt hr1
    have hr : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
    exact ⟨by simpa [disk] using hs,
      hyperbolicDistance_real_additive (by norm_num) hs hr hs0 hsr⟩

end ModifiedCartan
