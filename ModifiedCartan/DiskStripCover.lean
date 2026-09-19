import ModifiedCartan.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Complex
namespace ModifiedCartan

def diskCayley (z : ℂ) : ℂ := (1+z)/(1-z)
def halfPlaneCayleyInverse (w : ℂ) : ℂ := (w-1)/(w+1)

theorem diskCayley_den_ne_zero {z : ℂ} (hz : z ∈ disk 1) : 1-z ≠ 0 := by
  intro h
  have he : z = 1 := (sub_eq_zero.mp h).symm
  have hh : ‖z‖ < 1 := by simpa [disk] using hz
  simpa only [he,norm_one,lt_self_iff_false] using hh

theorem diskCayley_re_pos {z : ℂ} (hz : z ∈ disk 1) : 0 < (diskCayley z).re := by
  have hn : ‖z‖ < 1 := by simpa [disk] using hz
  have hs : normSq z < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have he : (diskCayley z).re = (1-normSq z)/normSq (1-z) := by
    simp only [diskCayley,Complex.div_re,Complex.add_re,Complex.one_re,Complex.add_im,
      Complex.one_im,Complex.sub_re,Complex.sub_im,normSq_apply]
    ring
  rw [he]
  exact div_pos (sub_pos.mpr hs) (normSq_pos.mpr (diskCayley_den_ne_zero hz))

theorem diskCayley_differentiableOn : DifferentiableOn ℂ diskCayley (disk 1) := by
  apply DifferentiableOn.div (by fun_prop) (by fun_prop)
  exact fun z hz => diskCayley_den_ne_zero hz

theorem halfPlaneCayley_den_ne_zero {w : ℂ} (hw : 0 < w.re) : w+1 ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at he
  linarith

theorem halfPlaneCayleyInverse_mem_disk {w : ℂ} (hw : 0 < w.re) :
    halfPlaneCayleyInverse w ∈ disk 1 := by
  have hs : ‖w-1‖^2 < ‖w+1‖^2 := by
    simp only [Complex.sq_norm,normSq_apply,Complex.sub_re,Complex.one_re,
      Complex.sub_im,Complex.one_im,Complex.add_re,Complex.add_im]
    nlinarith
  have hn : ‖w-1‖ < ‖w+1‖ := by nlinarith [norm_nonneg (w-1),norm_nonneg (w+1)]
  have hden : 0 < ‖w+1‖ := norm_pos_iff.mpr (halfPlaneCayley_den_ne_zero hw)
  simpa only [disk,mem_ball,dist_zero_right,halfPlaneCayleyInverse,norm_div] using
    (div_lt_one hden).mpr hn

theorem diskCayley_inverse {w : ℂ} (hw : 0 < w.re) :
    diskCayley (halfPlaneCayleyInverse w) = w := by
  have hd := halfPlaneCayley_den_ne_zero hw
  dsimp [diskCayley,halfPlaneCayleyInverse]
  field_simp
  <;> ring

theorem log_diskCayley_im_bounds {z : ℂ} (hz : z ∈ disk 1) :
    -(Real.pi/2) < (Complex.log (diskCayley z)).im ∧
      (Complex.log (diskCayley z)).im < Real.pi/2 := by
  rw [Complex.log_im]
  exact abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (diskCayley_re_pos hz)))

theorem log_diskCayley_differentiableOn :
    DifferentiableOn ℂ (fun z => Complex.log (diskCayley z)) (disk 1) := by
  intro z hz
  exact ((Complex.differentiableAt_log (Or.inl (diskCayley_re_pos hz))).comp z
    (diskCayley_differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt

theorem exp_re_pos_of_im_bounds {t : ℂ}
    (ht : -(Real.pi/2) < t.im ∧ t.im < Real.pi/2) : 0 < (Complex.exp t).re := by
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ht)

theorem log_diskCayley_surj_strip {t : ℂ}
    (ht : -(Real.pi/2) < t.im ∧ t.im < Real.pi/2) :
    ∃ z ∈ disk 1, Complex.log (diskCayley z) = t := by
  have hpos := exp_re_pos_of_im_bounds ht
  refine ⟨halfPlaneCayleyInverse (Complex.exp t),halfPlaneCayleyInverse_mem_disk hpos,?_⟩
  rw [diskCayley_inverse hpos]
  exact Complex.log_exp (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

end ModifiedCartan
