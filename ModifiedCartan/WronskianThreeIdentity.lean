import ModifiedCartan.TwoWronskian
import ModifiedCartan.LogDerivativeProducts

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

theorem wronskian_three (g : Fin 3 → ℂ → ℂ) (z : ℂ) :
    wronskian g z =
      g 0 z * (deriv (g 1) z * deriv (deriv (g 2)) z - deriv (g 2) z * deriv (deriv (g 1)) z) -
      g 1 z * (deriv (g 0) z * deriv (deriv (g 2)) z - deriv (g 2) z * deriv (deriv (g 0)) z) +
      g 2 z * (deriv (g 0) z * deriv (deriv (g 1)) z - deriv (g 1) z * deriv (deriv (g 0)) z) := by
  simp only [wronskian, Matrix.det_fin_three, Matrix.of_apply, Fin.val_zero,
    Fin.val_one, Fin.val_two, iteratedDeriv_succ', iteratedDeriv_zero]
  ring

theorem hasDerivAt_wronskian_two {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hdf : DifferentiableAt ℂ (deriv f) z) (hdg : DifferentiableAt ℂ (deriv g) z) :
    HasDerivAt (wronskian ![f,g])
      (f z * deriv (deriv g) z - g z * deriv (deriv f) z) z := by
  have hd := (hf.hasDerivAt.mul hdg.hasDerivAt).sub (hg.hasDerivAt.mul hdf.hasDerivAt)
  convert! hd using 1
  · funext w
    simp [wronskian_two]
  · ring

/-- The three-function derived fraction is the actual logarithmic derivative
of a quotient of two two-function Wronskians, with its exact sign. -/
theorem logDeriv_wronskian_ratio_three {g : Fin 3 → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, DifferentiableAt ℂ (g j) z)
    (hdg : ∀ j, DifferentiableAt ℂ (deriv (g j)) z)
    (h01 : wronskian ![g 0,g 1] z ≠ 0) (h02 : wronskian ![g 0,g 2] z ≠ 0) :
    logDeriv (fun w => wronskian ![g 0,g 1] w / wronskian ![g 0,g 2] w) z =
      -(g 0 z * wronskian g z) / (wronskian ![g 0,g 1] z * wronskian ![g 0,g 2] z) := by
  have hA := hasDerivAt_wronskian_two (hg 0) (hg 1) (hdg 0) (hdg 1)
  have hB := hasDerivAt_wronskian_two (hg 0) (hg 2) (hdg 0) (hdg 2)
  have hd := (hA.div hB h02).deriv
  simp only [Pi.div_def] at hd
  rw [logDeriv, Pi.div_apply, hd]
  field_simp
  simp only [wronskian_two, Matrix.cons_val_zero, Matrix.cons_val_one, wronskian_three]
  ring

theorem norm_logDeriv_wronskian_ratio_three {g : Fin 3 → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, DifferentiableAt ℂ (g j) z)
    (hdg : ∀ j, DifferentiableAt ℂ (deriv (g j)) z)
    (h01 : wronskian ![g 0,g 1] z ≠ 0) (h02 : wronskian ![g 0,g 2] z ≠ 0) :
    ‖logDeriv (fun w => wronskian ![g 0,g 1] w / wronskian ![g 0,g 2] w) z‖ =
      ‖g 0 z‖ * ‖wronskian g z‖ / (‖wronskian ![g 0,g 1] z‖ * ‖wronskian ![g 0,g 2] z‖) := by
  rw [logDeriv_wronskian_ratio_three hg hdg h01 h02]
  simp only [norm_div, norm_neg, norm_mul]

end ModifiedCartan
