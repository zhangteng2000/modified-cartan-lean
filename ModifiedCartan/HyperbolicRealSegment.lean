import ModifiedCartan.HyperbolicRadialSegment

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

theorem hyperbolic_real_endpoints_middle_im_zero {a b : ℝ}
    (ha : |a| < 1) (hb : |b| < 1) (hab : a ≤ b) {z : ℂ} (hz : z ∈ disk 1)
    (h : hyperbolicDistance (a : ℂ) z + hyperbolicDistance z (b : ℂ) =
      hyperbolicDistance (a : ℂ) (b : ℂ)) : z.im = 0 := by
  have han : ‖(a : ℂ)‖ < 1 := by simpa using ha
  have haD : (a : ℂ) ∈ disk 1 := by simpa [disk] using ha
  have hbD : (b : ℂ) ∈ disk 1 := by simpa [disk] using hb
  let f : ℂ → ℂ := fun w => -diskAutomorphism (a : ℂ) w
  have hfm : MapsTo f (disk 1) (disk 1) := by
    intro w hw
    simpa only [f, disk, mem_ball, dist_zero_right, norm_neg] using diskAutomorphism_mem_disk han hw
  have hfd (w t : ℂ) (hw : w ∈ disk 1) (ht : t ∈ disk 1) :
      hyperbolicDistance (f w) (f t) = hyperbolicDistance w t := by
    calc
      _ = hyperbolicDistance (diskAutomorphism (a : ℂ) w) (diskAutomorphism (a : ℂ) t) := by
        simpa only [neg_mul, one_mul] using
          hyperbolicDistance_rotation (ξ := (-1 : ℂ)) (by simp)
            (diskAutomorphism_mem_disk han hw) (diskAutomorphism_mem_disk han ht)
      _ = _ := hyperbolicDistance_diskAutomorphism han hw ht
  have hfa : f (a : ℂ) = 0 := by simp [f, diskAutomorphism_self]
  let r := (b - a) / (1 - a * b)
  have hden : 0 < 1 - a * b := by
    have hh := (mul_le_mul_of_nonneg_left hb.le (abs_nonneg a)).trans_lt (by simpa using ha)
    have hh' : a * b < 1 := (le_abs_self _).trans_lt (by simpa [abs_mul] using hh)
    linarith
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hab) hden.le
  have hfb : f (b : ℂ) = (r : ℂ) := by
    simp only [f, r, diskAutomorphism, conj_ofReal, ofReal_div, ofReal_sub, ofReal_one, ofReal_mul]
    ring
  have hr1 : r < 1 := by
    have hn : ‖f (b : ℂ)‖ < 1 := by simpa only [disk, mem_ball, dist_zero_right] using hfm hbD
    rwa [hfb, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hn
  have hadd : hyperbolicDistance 0 (f z) + hyperbolicDistance (f z) (r : ℂ) =
      hyperbolicDistance 0 (r : ℂ) := by
    calc
      _ = hyperbolicDistance (f (a : ℂ)) (f z) + hyperbolicDistance (f z) (f (b : ℂ)) := by
        rw [hfa, hfb]
      _ = hyperbolicDistance (a : ℂ) z + hyperbolicDistance z (b : ℂ) := by
        rw [hfd _ _ haD hz, hfd _ _ hz hbD]
      _ = hyperbolicDistance (a : ℂ) (b : ℂ) := h
      _ = _ := by rw [← hfd _ _ haD hbD, hfa, hfb]
  obtain ⟨s, _, _, hs⟩ := hyperbolic_radial_segment_rigidity hr0 hr1 (hfm hz) hadd
  have hs' : diskAutomorphism (a : ℂ) z = -(s : ℂ) := neg_eq_iff_eq_neg.mp hs
  have he : z = diskAutomorphism (a : ℂ) (-(s : ℂ)) := by
    calc
      _ = diskAutomorphism (a : ℂ) (diskAutomorphism (a : ℂ) z) :=
        (diskAutomorphism_involutive han hz).symm
      _ = _ := by rw [hs']
  rw [he]
  simp [diskAutomorphism, Complex.div_im]

theorem hyperbolicSegment_real {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) (hab : a ≤ b) :
    hyperbolicSegment (a : ℂ) (b : ℂ) = Complex.ofReal '' Icc a b := by
  ext z
  constructor
  · rintro ⟨hz, h⟩
    have him := hyperbolic_real_endpoints_middle_im_zero ha hb hab hz h
    have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
    have hs : |z.re| < 1 := by
      have hn : ‖z‖ < 1 := by simpa [disk] using hz
      rwa [he, Complex.norm_real, Real.norm_eq_abs] at hn
    have hadd : hyperbolicDistance (a : ℂ) (z.re : ℂ) +
        hyperbolicDistance (z.re : ℂ) (b : ℂ) = hyperbolicDistance (a : ℂ) (b : ℂ) := by
      rwa [← he]
    have has : a ≤ z.re := by
      by_contra hnot
      have hsa : z.re ≤ a := le_of_not_ge hnot
      rw [hyperbolicDistance_symm (a : ℂ) (z.re : ℂ),
        hyperbolicDistance_real_of_le hs ha hsa,
        hyperbolicDistance_real_of_le hs hb (hsa.trans hab),
        hyperbolicDistance_real_of_le ha hb hab] at hadd
      exact hnot ((hyperbolicRadialCoordinate_le_iff ha hs).mp (by linarith))
    have hsb : z.re ≤ b := by
      by_contra hnot
      have hbs : b ≤ z.re := le_of_not_ge hnot
      rw [hyperbolicDistance_real_of_le ha hs has,
        hyperbolicDistance_symm (z.re : ℂ) (b : ℂ),
        hyperbolicDistance_real_of_le hb hs hbs,
        hyperbolicDistance_real_of_le ha hb hab] at hadd
      exact hnot ((hyperbolicRadialCoordinate_le_iff hs hb).mp (by linarith))
    exact ⟨z.re, ⟨has, hsb⟩, he.symm⟩
  · rintro ⟨s, ⟨has, hsb⟩, rfl⟩
    have hs : |s| < 1 := abs_lt.mpr
      ⟨(abs_lt.mp ha).1.trans_le has, hsb.trans_lt (abs_lt.mp hb).2⟩
    exact ⟨by simpa [disk] using hs, hyperbolicDistance_real_additive ha hs hb has hsb⟩

end ModifiedCartan
