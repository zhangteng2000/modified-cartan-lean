import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

/-- Control the variation around an entire circle from a derivative bound in a
neighborhood of each circle point. No analyticity in the disk interior is required. -/
theorem circle_variation_bound {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R) (hD : 0 ≤ D)
    (hf : ∀ z ∈ sphere (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖deriv f z‖ ≤ D)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖f z - f (R : ℂ)‖ ≤ 2 * Real.pi * R * D := by
  have himage : circleMap 0 R '' Ioc 0 (2 * Real.pi) = sphere (0 : ℂ) R := by
    simpa [abs_of_pos hR] using image_circleMap_Ioc 0 R
  obtain ⟨θ, hθ, hθz⟩ := himage ▸ hz
  have hm : ∀ t : ℝ, circleMap 0 R t ∈ sphere (0 : ℂ) R := by
    intro t
    simpa [abs_of_pos hR] using circleMap_mem_sphere (0 : ℂ) R t
  have hder : ∀ t : ℝ, HasDerivAt (fun s => f (circleMap 0 R s))
      ((circleMap 0 R t * Complex.I) * deriv f (circleMap 0 R t)) t := by
    intro t
    exact ((hf _ (hm t)).hasDerivAt.scomp t (hasDerivAt_circleMap 0 R t))
  have hnorm : ∀ t : ℝ, ‖(circleMap 0 R t * Complex.I) * deriv f (circleMap 0 R t)‖ ≤ R * D := by
    intro t
    simp only [norm_mul, norm_I, mul_one]
    have hn : ‖circleMap 0 R t‖ = R := by simpa using hm t
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hbound _ (hm t)) hR.le
  have hvar := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Icc (0 : ℝ) (2 * Real.pi)) => (hder t).hasDerivWithinAt)
    (fun t _ => hnorm t) (convex_Icc (0 : ℝ) (2 * Real.pi))
    (show (0 : ℝ) ∈ Icc 0 (2 * Real.pi) by simp [Real.pi_pos.le])
    (show θ ∈ Icc (0 : ℝ) (2 * Real.pi) from ⟨hθ.1.le, hθ.2⟩)
  have hθabs : ‖θ - 0‖ ≤ 2 * Real.pi := by simpa [Real.norm_eq_abs, abs_of_pos hθ.1] using hθ.2
  have hfinal := hvar.trans (mul_le_mul_of_nonneg_left hθabs (mul_nonneg hR.le hD))
  change ‖f (circleMap 0 R θ) - f (circleMap 0 R 0)‖ ≤ _ at hfinal
  rw [hθz] at hfinal
  simpa [circleMap, mul_assoc, mul_comm, mul_left_comm] using hfinal

end ModifiedCartan
