import ModifiedCartan.WronskianThreeIdentity

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

theorem hasDerivAt_wronskian_three {g : Fin 3 → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, DifferentiableAt ℂ (g j) z)
    (hdg : ∀ j, DifferentiableAt ℂ (deriv (g j)) z)
    (hddg : ∀ j, DifferentiableAt ℂ (deriv (deriv (g j))) z) :
    HasDerivAt (wronskian g)
      (g 0 z * (deriv (g 1) z * deriv (deriv (deriv (g 2))) z -
          deriv (g 2) z * deriv (deriv (deriv (g 1))) z) -
        g 1 z * (deriv (g 0) z * deriv (deriv (deriv (g 2))) z -
          deriv (g 2) z * deriv (deriv (deriv (g 0))) z) +
        g 2 z * (deriv (g 0) z * deriv (deriv (deriv (g 1))) z -
          deriv (g 1) z * deriv (deriv (deriv (g 0))) z)) z := by
  have hd := (((hg 0).hasDerivAt.mul
      (((hdg 1).hasDerivAt.mul (hddg 2).hasDerivAt).sub
        ((hdg 2).hasDerivAt.mul (hddg 1).hasDerivAt))).sub
      ((hg 1).hasDerivAt.mul
      (((hdg 0).hasDerivAt.mul (hddg 2).hasDerivAt).sub
        ((hdg 2).hasDerivAt.mul (hddg 0).hasDerivAt)))).add
      ((hg 2).hasDerivAt.mul
      (((hdg 0).hasDerivAt.mul (hddg 1).hasDerivAt).sub
        ((hdg 1).hasDerivAt.mul (hddg 0).hasDerivAt)))
  convert! hd using 1
  · funext w
    simp [wronskian_three]
  · simp only [Pi.mul_apply, Pi.sub_apply]
    ring

/-- The next derived Wronskian fraction, required at five functions, is an
actual logarithmic derivative with its exact sign. -/
theorem logDeriv_wronskian_ratio_four {g : Fin 4 → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, DifferentiableAt ℂ (g j) z)
    (hdg : ∀ j, DifferentiableAt ℂ (deriv (g j)) z)
    (hddg : ∀ j, DifferentiableAt ℂ (deriv (deriv (g j))) z)
    (h012 : wronskian ![g 0,g 1,g 2] z ≠ 0)
    (h013 : wronskian ![g 0,g 1,g 3] z ≠ 0) :
    logDeriv (fun w => wronskian ![g 0,g 1,g 2] w / wronskian ![g 0,g 1,g 3] w) z =
      -(wronskian ![g 0,g 1] z * wronskian g z) /
        (wronskian ![g 0,g 1,g 2] z * wronskian ![g 0,g 1,g 3] z) := by
  have hA := hasDerivAt_wronskian_three (g := ![g 0,g 1,g 2])
    (by intro j; fin_cases j <;> simpa using hg _)
    (by intro j; fin_cases j <;> simpa using hdg _)
    (by intro j; fin_cases j <;> simpa using hddg _)
  have hB := hasDerivAt_wronskian_three (g := ![g 0,g 1,g 3])
    (by intro j; fin_cases j <;> simpa using hg _)
    (by intro j; fin_cases j <;> simpa using hdg _)
    (by intro j; fin_cases j <;> simpa using hddg _)
  have hd := (hA.div hB h013).deriv
  simp only [Pi.div_def] at hd
  rw [logDeriv, Pi.div_apply, hd]
  field_simp
  simp only [wronskian_two, wronskian_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  rw [wronskian, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four,
    Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply]
  norm_num [Fin.succAbove, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.lt_def, Fin.ext_iff, iteratedDeriv_succ', iteratedDeriv_zero]
  ring!

theorem norm_logDeriv_wronskian_ratio_four {g : Fin 4 → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, DifferentiableAt ℂ (g j) z)
    (hdg : ∀ j, DifferentiableAt ℂ (deriv (g j)) z)
    (hddg : ∀ j, DifferentiableAt ℂ (deriv (deriv (g j))) z)
    (h012 : wronskian ![g 0,g 1,g 2] z ≠ 0)
    (h013 : wronskian ![g 0,g 1,g 3] z ≠ 0) :
    ‖logDeriv (fun w => wronskian ![g 0,g 1,g 2] w / wronskian ![g 0,g 1,g 3] w) z‖ =
      ‖wronskian ![g 0,g 1] z‖ * ‖wronskian g z‖ /
        (‖wronskian ![g 0,g 1,g 2] z‖ * ‖wronskian ![g 0,g 1,g 3] z‖) := by
  rw [logDeriv_wronskian_ratio_four hg hdg hddg h012 h013]
  simp only [norm_div, norm_neg, norm_mul]

end ModifiedCartan
