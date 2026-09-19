import ModifiedCartan.SchwarzPick
import ModifiedCartan.SymmetricDiskSegments

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

def hyperbolicRadialCoordinate (r : ℝ) : ℝ := Real.log ((1 + r) / (1 - r))

theorem hyperbolicRadialCoordinate_le_iff {r s : ℝ} (hr : |r| < 1) (hs : |s| < 1) :
    hyperbolicRadialCoordinate r ≤ hyperbolicRadialCoordinate s ↔ r ≤ s := by
  have hr' := abs_lt.mp hr
  have hs' := abs_lt.mp hs
  unfold hyperbolicRadialCoordinate
  rw [Real.log_le_log_iff (div_pos (by linarith) (by linarith))
    (div_pos (by linarith) (by linarith)), div_le_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

theorem hyperbolicDistance_real_of_le {s t : ℝ} (hs : |s| < 1) (ht : |t| < 1) (hst : s ≤ t) :
    hyperbolicDistance (s : ℂ) (t : ℂ) =
      hyperbolicRadialCoordinate t - hyperbolicRadialCoordinate s := by
  have hs' := abs_lt.mp hs
  have ht' := abs_lt.mp ht
  have hprod : t * s < 1 := by
    have h := (mul_le_mul_of_nonneg_left hs.le (abs_nonneg t)).trans_lt
      (by simpa using ht)
    exact (le_abs_self (t * s)).trans_lt (by simpa [abs_mul] using h)
  have hden : 0 < 1 - t * s := by linarith
  have heq : diskAutomorphism (t : ℂ) (s : ℂ) = (((t - s) / (1 - t * s) : ℝ) : ℂ) := by
    simp [diskAutomorphism]
  have hz : (s : ℂ) ∈ disk 1 := by simpa [disk] using hs
  have htn : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hq : (t - s) / (1 - t * s) < 1 := by
    have h : ‖diskAutomorphism (t : ℂ) (s : ℂ)‖ < 1 := by
      simpa only [disk, mem_ball, dist_zero_right] using diskAutomorphism_mem_disk htn hz
    rw [heq] at h
    rwa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sub_nonneg.mpr hst) hden.le)] at h
  rw [hyperbolicDistance_eq_automorphism, heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hst) hden.le)]
  have hid : (1 + (t - s) / (1 - t * s)) / (1 - (t - s) / (1 - t * s)) =
      ((1 + t) / (1 - t)) / ((1 + s) / (1 - s)) := by
    field_simp
    <;> ring
  rw [hid, Real.log_div (div_ne_zero (by linarith : 1 + t ≠ 0) (by linarith : 1 - t ≠ 0))
    (div_ne_zero (by linarith : 1 + s ≠ 0) (by linarith : 1 - s ≠ 0))]
  rfl

theorem hyperbolicDistance_real_additive {s t u : ℝ}
    (hs : |s| < 1) (ht : |t| < 1) (hu : |u| < 1) (hst : s ≤ t) (htu : t ≤ u) :
    hyperbolicDistance (s : ℂ) (t : ℂ) + hyperbolicDistance (t : ℂ) (u : ℂ) =
      hyperbolicDistance (s : ℂ) (u : ℂ) := by
  rw [hyperbolicDistance_real_of_le hs ht hst, hyperbolicDistance_real_of_le ht hu htu,
    hyperbolicDistance_real_of_le hs hu (hst.trans htu)]
  ring

theorem diskSegmentMap_preserves_distance {a ξ z w : ℂ} {t : ℝ}
    (ha : ‖a‖ < 1) (hξ : ‖ξ‖ = 1) (ht : |t| < 1)
    (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    hyperbolicDistance (diskSegmentMap a ξ t z) (diskSegmentMap a ξ t w) =
      hyperbolicDistance z w := by
  have htn : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hzn : -z ∈ disk 1 := by simpa [disk] using hz
  have hwn : -w ∈ disk 1 := by simpa [disk] using hw
  have hz' := diskAutomorphism_mem_disk htn hzn
  have hw' := diskAutomorphism_mem_disk htn hwn
  have hzr : ξ * diskAutomorphism (t : ℂ) (-z) ∈ disk 1 := by
    simpa [disk, norm_mul, hξ] using hz'
  have hwr : ξ * diskAutomorphism (t : ℂ) (-w) ∈ disk 1 := by
    simpa [disk, norm_mul, hξ] using hw'
  unfold diskSegmentMap
  rw [hyperbolicDistance_diskAutomorphism ha hzr hwr,
    hyperbolicDistance_rotation hξ hz' hw', hyperbolicDistance_diskAutomorphism htn hzn hwn]
  simpa only [neg_mul, one_mul] using
    hyperbolicDistance_rotation (ξ := (-1 : ℂ)) (by simp) hz hw

theorem distance_bound_uniform_pseudoradius {d : ℝ} (hd : 0 < d) (hd3 : d < Real.log 3) :
    ∃ q : ℝ, 0 < q ∧ q < sharpRadius ∧ ∀ a b : ℂ,
      a ∈ disk 1 → b ∈ disk 1 → hyperbolicDistance a b ≤ d →
      ‖diskAutomorphism a b‖ ≤ symmetricPseudodistance q := by
  let r := (Real.exp d - 1) / (Real.exp d + 1)
  have he1 : 1 < Real.exp d := by simpa using Real.exp_lt_exp.mpr hd
  have he3 : Real.exp d < 3 := by
    exact (Real.exp_lt_exp.mpr hd3).trans_eq (Real.exp_log (by norm_num))
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact (div_pos (by linarith) (by positivity)).le
  have hrh : r < 1 / 2 := by
    dsimp [r]
    apply (div_lt_iff₀ (by positivity : 0 < Real.exp d + 1)).mpr
    linarith
  obtain ⟨q, hq, hqr, hrq⟩ := exists_uniform_symmetric_radius hr0 hrh
  refine ⟨q, hq, hqr, ?_⟩
  intro a b ha hb hab
  have hn : ‖diskAutomorphism a b‖ < 1 := by
    simpa [disk] using diskAutomorphism_mem_disk (show ‖a‖ < 1 by simpa [disk] using ha) hb
  have hden : 0 < 1 - ‖diskAutomorphism a b‖ := by linarith
  rw [hyperbolicDistance_symm a b, hyperbolicDistance_eq_automorphism] at hab
  have hratio : (1 + ‖diskAutomorphism a b‖) / (1 - ‖diskAutomorphism a b‖) ≤ Real.exp d := by
    have h := Real.exp_le_exp.mpr hab
    rwa [Real.exp_log (div_pos (by positivity) hden)] at h
  have hmul := (div_le_iff₀ hden).mp hratio
  apply le_trans _ hrq.le
  dsimp [r]
  apply (le_div_iff₀ (by positivity : 0 < Real.exp d + 1)).mpr
  nlinarith

end ModifiedCartan
