import ModifiedCartan.HyperbolicCoordinates
import Mathlib.Topology.Order.LeftRightNhds

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Complex Metric Set Real Filter Topology
namespace ModifiedCartan

theorem hyperbolicRadialCoordinate_neg {r : ℝ} (_hr : |r| < 1) :
    hyperbolicRadialCoordinate (-r) = -hyperbolicRadialCoordinate r := by
  unfold hyperbolicRadialCoordinate
  rw [show (1 + -r) / (1 - -r) = ((1 + r) / (1 - r))⁻¹ by simp [sub_eq_add_neg]]
  exact Real.log_inv _

theorem hyperbolicDistance_opposite {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    hyperbolicDistance ((-r : ℝ) : ℂ) (r : ℂ) = 2 * hyperbolicRadialCoordinate r := by
  have hr : |r| < 1 := by simpa [abs_of_nonneg hr0] using hr1
  rw [hyperbolicDistance_real_of_le (by simpa using hr) hr (by linarith),
    hyperbolicRadialCoordinate_neg hr]
  ring

theorem disk_pseudodiameter {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) {a z : ℂ}
    (ha : ‖a‖ ≤ R) (hz : ‖z‖ ≤ R) : ‖diskAutomorphism a z‖ ≤ symmetricPseudodistance R := by
  have har := (sq_le_sq₀ (norm_nonneg a) hR0).mpr ha
  have hzr := (sq_le_sq₀ (norm_nonneg z) hR0).mpr hz
  have hR2 : R ^ 2 < 1 := by nlinarith
  have hnum : ‖z - a‖ ≤ 2 * R := by linarith [norm_sub_le z a]
  have hnum2 : ‖z - a‖ ^ 2 ≤ 4 * R ^ 2 := by
    have hh := (sq_le_sq₀ (norm_nonneg (z - a)) (by positivity : 0 ≤ 2 * R)).mpr hnum
    nlinarith only [hh]
  have hprod : (1 - R ^ 2) ^ 2 ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    rw [pow_two]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by nlinarith)
  have hid := blaschke_norm_identity 1 a z
  simp only [one_pow, Complex.ofReal_one, one_mul] at hid
  have hden : 0 < ‖1 - conj a * z‖ := norm_pos_iff.mpr
    (diskAutomorphism_denominator_ne_zero (ha.trans_lt hR1) (hz.trans hR1.le))
  have hcross : (1 + R ^ 2) * ‖z - a‖ ≤ 2 * R * ‖1 - conj a * z‖ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have hh := mul_le_mul_of_nonneg_left hnum2 (sq_nonneg (1 - R ^ 2))
    have hp := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 4 * R ^ 2)
    nlinarith only [hh, hp, hid]
  rw [diskAutomorphism, norm_div, norm_sub_rev a z, symmetricPseudodistance]
  apply (div_le_div_iff₀ hden (by positivity : 0 < 1 + R ^ 2)).mpr
  nlinarith only [hcross]

theorem disk_hyperbolicDiameter {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    HasHyperbolicDiameterLE (disk R) (2 * hyperbolicRadialCoordinate R) := by
  intro z hz w hw
  have hzn : ‖z‖ < R := by simpa [disk] using hz
  have hwn : ‖w‖ < R := by simpa [disk] using hw
  have hq := disk_pseudodiameter hR0 hR1 hwn.le hzn.le
  have hq0 : 0 ≤ symmetricPseudodistance R := by unfold symmetricPseudodistance; positivity
  have hq1 : symmetricPseudodistance R < 1 := by
    unfold symmetricPseudodistance
    apply (div_lt_one (by positivity : 0 < 1 + R ^ 2)).mpr
    nlinarith [sq_pos_of_pos (show 0 < 1 - R by linarith)]
  have hδ1 : ‖diskAutomorphism w z‖ < 1 := hq.trans_lt hq1
  have hbound : hyperbolicRadialCoordinate ‖diskAutomorphism w z‖ ≤
      hyperbolicRadialCoordinate (symmetricPseudodistance R) :=
    (hyperbolicRadialCoordinate_le_iff (by simpa only [abs_norm] using hδ1)
      (by simpa only [abs_of_nonneg hq0] using hq1)).mpr hq
  have he := hyperbolicDistance_opposite hR0 hR1
  rw [hyperbolicDistance_eq_automorphism, diskAutomorphism_real_opposite,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0] at he
  rw [hyperbolicDistance_eq_automorphism]
  exact hbound.trans_eq he

theorem hyperbolicRadialCoordinate_continuousAt {r : ℝ} (hr : |r| < 1) :
    ContinuousAt hyperbolicRadialCoordinate r := by
  have hh := abs_lt.mp hr
  unfold hyperbolicRadialCoordinate
  apply ContinuousAt.log
  · exact (continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) (by linarith)
  · exact (div_pos (by linarith : 0 < 1 + r) (by linarith : 0 < 1 - r)).ne'

/-- The supremal Poincare diameter of the open radius-R disk is exactly
2 log((1+R)/(1-R)); endpoints on the Euclidean boundary are not assumed present. -/
theorem disk_hyperbolicDiameter_iff {R d : ℝ} (hR0 : 0 < R) (hR1 : R < 1) :
    HasHyperbolicDiameterLE (disk R) d ↔ 2 * hyperbolicRadialCoordinate R ≤ d := by
  constructor
  · intro h
    have hc := (hyperbolicRadialCoordinate_continuousAt
      (show |R| < 1 by simpa [abs_of_pos hR0] using hR1)).const_mul 2
    apply le_of_tendsto (hc.tendsto.mono_left (show 𝓝[<] R ≤ 𝓝 R from nhdsWithin_le_nhds))
    filter_upwards [Ioo_mem_nhdsLT hR0] with t ht
    have htm : ((-t : ℝ) : ℂ) ∈ disk R := by simpa [disk, abs_of_pos ht.1] using ht.2
    have htp : (t : ℂ) ∈ disk R := by simpa [disk, abs_of_pos ht.1] using ht.2
    simpa only [hyperbolicDistance_opposite ht.1.le (ht.2.trans hR1)] using h _ htm _ htp
  · intro h z hz w hw
    exact (disk_hyperbolicDiameter hR0.le hR1 z hz w hw).trans h

end ModifiedCartan
