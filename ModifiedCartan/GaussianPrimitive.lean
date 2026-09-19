import ModifiedCartan.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory Metric Set Filter Topology
namespace ModifiedCartan

def gaussianKernel (n : ℝ) (z : ℂ) : ℂ := Complex.exp (-(n : ℂ) * z ^ 2)

def gaussianPrimitive (n : ℝ) (z : ℂ) : ℂ :=
  Complex.wedgeIntegral 0 z (gaussianKernel n)

/-- The manuscript's normalized entire Gaussian integral. The wedge integral
is a concrete path integral from zero to z. -/
def gaussianTransition (n : ℝ) (z : ℂ) : ℂ :=
  1 / 2 + (Real.sqrt (n / Real.pi) : ℂ) * gaussianPrimitive n z

theorem gaussianKernel_differentiable (n : ℝ) : Differentiable ℂ (gaussianKernel n) := by
  unfold gaussianKernel
  fun_prop

theorem gaussianPrimitive_hasDerivAt (n : ℝ) (z : ℂ) :
    HasDerivAt (gaussianPrimitive n) (gaussianKernel n z) z := by
  have hd := (gaussianKernel_differentiable n).differentiableOn
    (s := ball (0 : ℂ) (‖z‖ + 1))
  exact hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn (by simp)

theorem gaussianPrimitive_zero (n : ℝ) : gaussianPrimitive n 0 = 0 := by
  simp [gaussianPrimitive, Complex.wedgeIntegral]

theorem gaussianTransition_zero (n : ℝ) : gaussianTransition n 0 = 1 / 2 := by
  simp [gaussianTransition, gaussianPrimitive_zero]

theorem gaussianTransition_hasDerivAt (n : ℝ) (z : ℂ) :
    HasDerivAt (gaussianTransition n)
      ((Real.sqrt (n / Real.pi) : ℂ) * gaussianKernel n z) z := by
  exact ((gaussianPrimitive_hasDerivAt n z).const_mul _).const_add _

theorem gaussianTransition_entire (n : ℝ) : Differentiable ℂ (gaussianTransition n) :=
  fun z => (gaussianTransition_hasDerivAt n z).differentiableAt

theorem gaussianTransition_symmetry (n : ℝ) (z : ℂ) :
    gaussianTransition n z + gaussianTransition n (-z) = 1 := by
  have hd (w : ℂ) : HasDerivAt
      (fun w => gaussianTransition n w + gaussianTransition n (-w)) 0 w := by
    have hh := (gaussianTransition_hasDerivAt n w).add
      ((gaussianTransition_hasDerivAt n (-w)).comp w (hasDerivAt_id w).neg)
    convert! hh using 1 <;> simp [gaussianKernel]
  have he := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  norm_num [gaussianTransition_zero] at he ⊢
  exact he

theorem gaussianKernel_norm (n : ℝ) (z : ℂ) :
    ‖gaussianKernel n z‖ = Real.exp (-n * (z.re ^ 2 - z.im ^ 2)) := by
  rw [gaussianKernel, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re]

theorem gaussianKernel_even (n : ℝ) (z : ℂ) : gaussianKernel n (-z) = gaussianKernel n z := by
  simp [gaussianKernel]

theorem gaussianPrimitive_real (n x : ℝ) :
    gaussianPrimitive n (x : ℂ) = ∫ t in (0 : ℝ)..x, gaussianKernel n (t : ℂ) := by
  simp [gaussianPrimitive, Complex.wedgeIntegral]

/-- Primitive increments are given by the same actual rectangular path integral. -/
theorem gaussianPrimitive_sub (n : ℝ) (z w : ℂ) :
    gaussianPrimitive n z - gaussianPrimitive n w = Complex.wedgeIntegral w z (gaussianKernel n) := by
  have hd (v : ℂ) : HasDerivAt
      (fun v => Complex.wedgeIntegral w v (gaussianKernel n)) (gaussianKernel n v) v := by
    have hh := (gaussianKernel_differentiable n).differentiableOn
      (s := ball w (dist v w + 1))
    exact hh.isConservativeOn.hasDerivAt_wedgeIntegral hh.continuousOn (by simp)
  have he (v : ℂ) : HasDerivAt
      (fun v => gaussianPrimitive n v - Complex.wedgeIntegral w v (gaussianKernel n)) 0 v := by
    convert! (gaussianPrimitive_hasDerivAt n v).sub (hd v) using 1 <;> simp
  have hc := is_const_of_deriv_eq_zero (fun v => (he v).differentiableAt)
    (fun v => (he v).deriv) z w
  simp only [Complex.wedgeIntegral, intervalIntegral.integral_same, smul_zero, add_zero,
    sub_zero] at hc
  unfold Complex.wedgeIntegral
  linear_combination hc

end ModifiedCartan
