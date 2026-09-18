import ModifiedCartan.CauchyBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.LogDeriv

noncomputable section
set_option autoImplicit false
open Complex Metric Set
namespace ModifiedCartan

/-- A zero-free holomorphic function on a disk has a holomorphic logarithm.
The branch is constructed by integrating its logarithmic derivative. -/
theorem exists_holomorphic_log_on_disk {Q : ℂ → ℂ} {T : ℝ} (hT : 0 < T)
    (hQ : DifferentiableOn ℂ Q (disk T)) (hnz : ∀ z ∈ disk T, Q z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (disk T) ∧ L 0 = Complex.log (Q 0) ∧
      (∀ z ∈ disk T, Complex.exp (L z) = Q z) ∧
      (∀ z ∈ disk T, deriv L z = logDeriv Q z) := by
  have hld : DifferentiableOn ℂ (logDeriv Q) (disk T) :=
    (hQ.deriv isOpen_ball).div hQ hnz
  obtain ⟨L, hL0, hLder⟩ := hld.isExactOn_ball.with_val_at 0 (Complex.log (Q 0))
  have hL : DifferentiableOn ℂ L (disk T) := fun z hz => (hLder z hz).differentiableAt.differentiableWithinAt
  let P : ℂ → ℂ := fun z => Q z * Complex.exp (-L z)
  have hPder : ∀ z ∈ disk T, HasDerivAt P 0 z := by
    intro z hz
    have he := ((hQ z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.mul
      ((hLder z hz).neg.cexp)
    have hc : deriv Q z * Complex.exp (-L z) + Q z *
        (Complex.exp (-L z) * -logDeriv Q z) = 0 := by
      rw [logDeriv_apply]
      field_simp [hnz z hz]
      ring
    have he' : HasDerivAt P (deriv Q z * Complex.exp (-L z) + Q z *
        (Complex.exp (-L z) * -logDeriv Q z)) z := he
    rwa [hc] at he'
  have hz0 : (0 : ℂ) ∈ disk T := by simpa [disk]
  have hP0 : P 0 = 1 := by
    dsimp [P]
    rw [hL0, Complex.exp_neg, Complex.exp_log (hnz 0 hz0), mul_inv_cancel₀ (hnz 0 hz0)]
  refine ⟨L, hL, hL0, ?_, fun z hz => (hLder z hz).deriv⟩
  intro z hz
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) T).isPreconnected
    (fun v hv => (hPder v hv).differentiableAt.differentiableWithinAt) (fun v hv => (hPder v hv).deriv) hz hz0
  rw [hP0] at he
  change Q z * Complex.exp (-L z) = 1 at he
  rw [Complex.exp_neg, ← div_eq_mul_inv] at he
  exact ((div_eq_one_iff_eq (Complex.exp_ne_zero _)).mp he).symm

theorem holomorphic_log_real_part {Q L : ℂ → ℂ} {U : Set ℂ}
    (he : ∀ z ∈ U, Complex.exp (L z) = Q z) {z : ℂ} (hz : z ∈ U) :
    (L z).re = Real.log ‖Q z‖ := by
  rw [← he z hz, Complex.norm_exp, Real.log_exp]

end ModifiedCartan
