import ModifiedCartan.Basic
import Mathlib.Analysis.Convex.Topology

noncomputable section
set_option autoImplicit false
open Filter Topology Complex Metric Set
namespace ModifiedCartan

def segmentRectangle (T h : ℝ) : Set ℂ :=
  {z | |z.re| < T + h ∧ |z.im| < h}

theorem segmentRectangle_open (T h : ℝ) : IsOpen (segmentRectangle T h) :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)

theorem segmentRectangle_convex (T h : ℝ) : Convex ℝ (segmentRectangle T h) := by
  have he : segmentRectangle T h =
      (Complex.reLm ⁻¹' Ioo (-(T + h)) (T + h)) ∩ (Complex.imLm ⁻¹' Ioo (-h) h) := by
    ext z
    simp only [segmentRectangle, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo,
      abs_lt]
    rfl
  rw [he]
  exact ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
    ((convex_Ioo _ _).linear_preimage Complex.imLm)

theorem segmentRectangle_endpoints {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) :
    ((-T : ℝ) : ℂ) ∈ segmentRectangle T h ∧ (T : ℂ) ∈ segmentRectangle T h := by
  simp only [segmentRectangle, mem_ofPred_eq, ofReal_re, ofReal_im, abs_zero,
    abs_neg, abs_of_nonneg hT]
  exact ⟨⟨by linarith, hh⟩, ⟨by linarith, hh⟩⟩

theorem segmentRectangle_norm {T h : ℝ} {z : ℂ} (hz : z ∈ segmentRectangle T h) :
    ‖z‖ < T + 2 * h := by
  have hn := Complex.norm_le_abs_re_add_abs_im z
  linarith [hz.1, hz.2]

theorem segmentRectangle_near_segment {T t h : ℝ} (ht : 0 ≤ t) (hh : 0 < h)
    (hclose : |t - T| < h) {z : ℂ} (hz : z ∈ segmentRectangle T h) :
    ∃ s : ℝ, |s| ≤ t ∧ ‖z - (s : ℂ)‖ < 3 * h := by
  have hbounds := abs_lt.mp hclose
  have hre := abs_lt.mp hz.1
  have hchoose : ∃ s : ℝ, |s| ≤ t ∧ |z.re - s| < 2 * h := by
    by_cases hlo : z.re < -t
    · refine ⟨-t, by simp [abs_of_nonneg ht], ?_⟩
      rw [abs_of_neg (by linarith : z.re - -t < 0)]
      linarith
    · by_cases hhi : t < z.re
      · refine ⟨t, by simp [abs_of_nonneg ht], ?_⟩
        rw [abs_of_pos (sub_pos.mpr hhi)]
        linarith
      · exact ⟨z.re, abs_le.mpr ⟨by linarith, by linarith⟩, by simp; positivity⟩
  obtain ⟨s, hs, hsre⟩ := hchoose
  refine ⟨s, hs, ?_⟩
  have hn := Complex.norm_le_abs_re_add_abs_im (z - (s : ℂ))
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hn
  linarith [hz.2]

theorem segmentRectangle_eventually_near {T h : ℝ} (hh : 0 < h) {t : ℕ → ℝ}
    (ht : ∀ n, 0 ≤ t n) (hlim : Tendsto t atTop (𝓝 T)) :
    ∀ᶠ n in atTop, ∀ z ∈ segmentRectangle T h,
      ∃ s : ℝ, |s| ≤ t n ∧ ‖z - (s : ℂ)‖ < 3 * h := by
  have hc : ∀ᶠ n in atTop, |t n - T| < h := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hlim h hh
  exact hc.mono (fun n hn z hz => segmentRectangle_near_segment (ht n) hh hn hz)

end ModifiedCartan
