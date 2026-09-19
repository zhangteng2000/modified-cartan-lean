import ModifiedCartan.CircleVariation
import ModifiedCartan.CartanMergeAnnulus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- The logarithm of the modulus has the expected real derivative without
requiring a global choice of a complex logarithm. -/
theorem hasDerivAt_log_norm {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v t) (hne : f t ≠ 0) :
    HasDerivAt (fun s => Real.log ‖f s‖) (v / f t).re t := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hne with hp | hn
  · simpa only [Function.comp_def, Complex.reCLM_apply, Complex.log_re] using (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf.clog_real hp))
  · simpa only [Function.comp_def, Complex.reCLM_apply, Pi.neg_apply, norm_neg, Complex.log_re, neg_div_neg_eq] using (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf.neg.clog_real hn))

/-- Bounded logarithmic derivative controls the logarithmic modulus around
an entire circle, even when no logarithm exists on the enclosed annulus. -/
theorem circle_log_norm_variation {f : ℂ → ℂ} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ∀ z ∈ sphere (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hnz : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖logDeriv f z‖ ≤ C)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    |Real.log ‖f z‖ - Real.log ‖f (R : ℂ)‖| ≤ 2 * Real.pi * R * C := by
  have himage : circleMap 0 R '' Ioc 0 (2 * Real.pi) = sphere (0 : ℂ) R := by
    simpa [abs_of_pos hR] using image_circleMap_Ioc 0 R
  obtain ⟨θ, hθ, hθz⟩ := himage ▸ hz
  have hm : ∀ t : ℝ, circleMap 0 R t ∈ sphere (0 : ℂ) R := by
    intro t
    simpa [abs_of_pos hR] using circleMap_mem_sphere (0 : ℂ) R t
  have hder : ∀ t : ℝ, HasDerivAt (fun s => Real.log ‖f (circleMap 0 R s)‖)
      (((circleMap 0 R t * Complex.I) * deriv f (circleMap 0 R t)) /
        f (circleMap 0 R t)).re t := by
    intro t
    exact hasDerivAt_log_norm ((hf _ (hm t)).hasDerivAt.scomp t (hasDerivAt_circleMap 0 R t))
      (hnz _ (hm t))
  have hnorm : ∀ t : ℝ, ‖(((circleMap 0 R t * Complex.I) * deriv f (circleMap 0 R t)) /
        f (circleMap 0 R t)).re‖ ≤ R * C := by
    intro t
    apply (Complex.abs_re_le_norm _).trans
    rw [mul_div_assoc, norm_mul, norm_mul, Complex.norm_I, mul_one]
    change ‖circleMap 0 R t‖ * ‖logDeriv f (circleMap 0 R t)‖ ≤ R*C
    have hr : ‖circleMap 0 R t‖ = R := by simpa using hm t
    rw [hr]
    exact mul_le_mul_of_nonneg_left (hbound _ (hm t)) hR.le
  have hv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Icc (0 : ℝ) (2*Real.pi)) => (hder t).hasDerivWithinAt)
    (fun t _ => hnorm t) (convex_Icc (0 : ℝ) (2*Real.pi))
    (show (0 : ℝ) ∈ Icc 0 (2*Real.pi) by simp [Real.pi_pos.le])
    (show θ ∈ Icc (0 : ℝ) (2*Real.pi) from ⟨hθ.1.le,hθ.2⟩)
  have hθabs : ‖θ-0‖ ≤ 2*Real.pi := by simpa [Real.norm_eq_abs, abs_of_pos hθ.1] using hθ.2
  have hh := hv.trans (mul_le_mul_of_nonneg_left hθabs (mul_nonneg hR.le hC))
  change ‖Real.log ‖f (circleMap 0 R θ)‖ - Real.log ‖f (circleMap 0 R 0)‖‖ ≤ _ at hh
  rw [hθz] at hh
  simpa [circleMap, Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using hh

/-- Logarithmic modulus variation on a radial interval. -/
theorem radial_log_norm_variation {f : ℂ → ℂ} {α β C : ℝ}
    (hα : 0 ≤ α) (hf : ∀ z ∈ complexAnnulus α β, DifferentiableAt ℂ f z)
    (hnz : ∀ z ∈ complexAnnulus α β, f z ≠ 0)
    (hbound : ∀ z ∈ complexAnnulus α β, ‖logDeriv f z‖ ≤ C)
    {r s : ℝ} (hr : r ∈ Ioo α β) (hs : s ∈ Ioo α β) :
    |Real.log ‖f (r : ℂ)‖ - Real.log ‖f (s : ℂ)‖| ≤ C * |r-s| := by
  have hm : ∀ t ∈ Ioo α β, (t : ℂ) ∈ complexAnnulus α β := by
    intro t ht
    simpa [complexAnnulus, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hα.trans_lt ht.1)] using ht
  have hd : ∀ t ∈ Ioo α β, HasDerivAt (fun s : ℝ => Real.log ‖f (s : ℂ)‖)
      (logDeriv f (t : ℂ)).re t := by
    intro t ht
    exact hasDerivAt_log_norm (hf _ (hm t ht)).hasDerivAt.comp_ofReal (hnz _ (hm t ht))
  have hb : ∀ t ∈ Ioo α β, ‖(logDeriv f (t : ℂ)).re‖ ≤ C := by
    intro t ht
    exact (Complex.abs_re_le_norm _).trans (hbound _ (hm t ht))
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt) hb (convex_Ioo α β) hs hr

/-- Uniform modulus comparison on a circular annulus. The estimate uses
logarithmic moduli along paths and does not postulate a single-valued logarithm. -/
theorem annulus_log_norm_variation {f : ℂ → ℂ} {α β C : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hf : ∀ z ∈ complexAnnulus α β, DifferentiableAt ℂ f z)
    (hnz : ∀ z ∈ complexAnnulus α β, f z ≠ 0)
    (hbound : ∀ z ∈ complexAnnulus α β, ‖logDeriv f z‖ ≤ C)
    {z w : ℂ} (hz : z ∈ complexAnnulus α β) (hw : w ∈ complexAnnulus α β) :
    |Real.log ‖f z‖ - Real.log ‖f w‖| ≤ (4 * Real.pi * β + β - α) * C := by
  have hcirc : ∀ v ∈ complexAnnulus α β,
      |Real.log ‖f v‖ - Real.log ‖f (‖v‖ : ℂ)‖| ≤ 2 * Real.pi * β * C := by
    intro v hv
    have hs : sphere (0 : ℂ) ‖v‖ ⊆ complexAnnulus α β := by
      intro u hu
      have he : ‖u‖ = ‖v‖ := by simpa using hu
      simpa only [complexAnnulus, mem_ofPred_eq, he] using hv
    have hb := circle_log_norm_variation (hα.trans_lt hv.1) hC
      (fun u hu => hf u (hs hu)) (fun u hu => hnz u (hs hu))
      (fun u hu => hbound u (hs hu)) (show v ∈ sphere (0 : ℂ) ‖v‖ by simp)
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv.2.le (by positivity)) hC)
  have hr := radial_log_norm_variation hα hf hnz hbound hz hw
  have hd : |‖z‖ - ‖w‖| ≤ β-α := abs_sub_le_iff.mpr ⟨by linarith [hz.2,hw.1], by linarith [hw.2,hz.1]⟩
  have hp := hr.trans (mul_le_mul_of_nonneg_left hd hC)
  have ht := (abs_sub_le (Real.log ‖f z‖) (Real.log ‖f (‖z‖ : ℂ)‖) (Real.log ‖f w‖)).trans
    (add_le_add (le_refl _) (abs_sub_le (Real.log ‖f (‖z‖ : ℂ)‖) (Real.log ‖f (‖w‖ : ℂ)‖) (Real.log ‖f w‖)))
  have hzw := hcirc z hz
  have hww := hcirc w hw
  rw [abs_sub_comm (Real.log ‖f (‖w‖ : ℂ)‖)] at ht
  nlinarith

/-- On each such annulus either the function or its reciprocal is uniformly
bounded by an explicit constant independent of its anchor value. -/
theorem annulus_logDerivative_alternative {f : ℂ → ℂ} {α β C : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hf : ∀ z ∈ complexAnnulus α β, DifferentiableAt ℂ f z)
    (hnz : ∀ z ∈ complexAnnulus α β, f z ≠ 0)
    (hbound : ∀ z ∈ complexAnnulus α β, ‖logDeriv f z‖ ≤ C) :
    (∀ z ∈ complexAnnulus α β, ‖f z‖ ≤ 1) ∨
      ∀ z ∈ complexAnnulus α β, ‖(f z)⁻¹‖ ≤ Real.exp ((4 * Real.pi * β + β - α) * C) := by
  by_cases hb : ∀ z ∈ complexAnnulus α β, ‖f z‖ ≤ 1
  · exact Or.inl hb
  · right
    push Not at hb
    obtain ⟨w, hw, hw1⟩ := hb
    intro z hz
    have hv := annulus_log_norm_variation hα hC hf hnz hbound hw hz
    have hl : 0 ≤ Real.log ‖f w‖ := Real.log_nonneg hw1.le
    have hlog : -Real.log ‖f z‖ ≤ (4 * Real.pi * β + β - α) * C := by
      have := le_abs_self (Real.log ‖f w‖ - Real.log ‖f z‖)
      linarith
    rw [norm_inv, ← Real.exp_log (inv_pos.mpr (norm_pos_iff.mpr (hnz z hz))), Real.log_inv]
    exact Real.exp_le_exp.mpr hlog

end ModifiedCartan

