import ModifiedCartan.Harmonic
import ModifiedCartan.Kernel

noncomputable section
open Complex InnerProductSpace Metric Real Filter Topology
namespace ModifiedCartan

def twoPointMinus (t s : ℝ) : ℝ := (1 - t) * (1 - s) / ((1 + t) * (1 + s))
def twoPointPlus (t s : ℝ) : ℝ := (1 - t) * (1 + s) / ((1 + t) * (1 - s))

theorem poissonKernel_real_on_circle {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) R) (a : ℝ) :
    _root_.poissonKernel 0 ((R * a : ℝ) : ℂ) z = poissonKernel a (z.re / R) := by
  have hzN : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz
  have hd : ‖z - ((R * a : ℝ) : ℂ)‖ ^ 2 = R ^ 2 * poissonDenom a (z.re / R) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq, hzN]
    simp only [Complex.normSq_ofReal, Complex.conj_ofReal, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    dsimp [poissonDenom]
    field_simp
    ring
  rw [_root_.poissonKernel, sub_zero, sub_zero, hd, hzN]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [show R ^ 2 - (R * a) ^ 2 = R ^ 2 * (1 - a ^ 2) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hR.ne')

theorem twoPointKernel_eq_combination {t s c : ℝ} (ht : |t| < 1) (hs : |s| < 1) :
    twoPointKernel t s c =
      twoPointMinus t s * poissonKernel (-t) c + twoPointPlus t s * poissonKernel t c := by
  have htp : 1 + t ≠ 0 := by have := (abs_lt.mp ht).1; linarith
  have hsp : 1 + s ≠ 0 := by have := (abs_lt.mp hs).1; linarith
  have hsm : 1 - s ≠ 0 := by have := (abs_lt.mp hs).2; linarith
  have hden : poissonDenom (-t) c = poissonDenom t (-c) := by dsimp [poissonDenom]; ring
  dsimp [twoPointKernel, twoPointMinus, twoPointPlus, weightedKernel, poissonKernel]
  rw [hden]
  field_simp
  ring

theorem scaled_real_mem_ball {R a : ℝ} (hR : 0 < R) (ha : |a| < 1) :
    ((R * a : ℝ) : ℂ) ∈ ball (0 : ℂ) R := by
  rw [mem_ball_iff_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hR]
  nlinarith

/-- Integrate the kernel comparison on a circle of any positive radius. -/
theorem harmonic_two_point_on_closedBall {U : ℂ → ℝ} {R t s ε : ℝ}
    (hR : 0 < R) (hU : HarmonicContOnCl U (ball 0 R))
    (hUb : ∀ z ∈ sphere (0 : ℂ) R, 0 ≤ U z)
    (ht : |t| < 1) (hs : |s| < 1)
    (hkernel : ∀ c : ℝ, |c| ≤ 1 → (1 + ε) * poissonKernel s c ≤ twoPointKernel t s c) :
    (1 + ε) * U ((R * s : ℝ) : ℂ) ≤
      twoPointMinus t s * U ((R * (-t) : ℝ) : ℂ) +
      twoPointPlus t s * U ((R * t : ℝ) : ℂ) := by
  have hUi : ContinuousOn U (sphere (0 : ℂ) |R|) := by
    simpa [abs_of_pos hR] using hU.continuousOn_ball.mono sphere_subset_closedBall
  have hi : ∀ a : ℝ, |a| < 1 →
      CircleIntegrable (_root_.poissonKernel 0 ((R * a : ℝ) : ℂ) • U) 0 R := by
    intro a ha
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact ((Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere (scaled_real_mem_ball hR ha))).smul hUi).circleIntegrable'
  have his := hi s hs
  have hit := hi t ht
  have hint := hi (-t) (by simpa using ht)
  have hmono := circleAverage_mono (his.const_smul (a := 1 + ε))
    ((hint.const_smul (a := twoPointMinus t s)).add
      (hit.const_smul (a := twoPointPlus t s))) (fun z hz => ?_)
  · rw [circleAverage_smul,
      circleAverage_add (hint.const_smul (a := twoPointMinus t s))
        (hit.const_smul (a := twoPointPlus t s)),
      circleAverage_smul, circleAverage_smul,
      hU.circleAverage_poissonKernel_smul (scaled_real_mem_ball hR hs),
      hU.circleAverage_poissonKernel_smul (scaled_real_mem_ball hR (by simpa using ht)),
      hU.circleAverage_poissonKernel_smul (scaled_real_mem_ball hR ht)] at hmono
    exact hmono
  · have hz' : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hz
    have hzN : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm] using hz'
    have hc : |z.re / R| ≤ 1 := by
      rw [abs_div, abs_of_pos hR, div_le_one hR]
      exact (Complex.abs_re_le_norm z).trans_eq hzN
    have hb := mul_le_mul_of_nonneg_right (hkernel (z.re / R) hc) (hUb z hz')
    rw [twoPointKernel_eq_combination ht hs] at hb
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.mul_apply]
    rw [poissonKernel_real_on_circle hR hz' s,
      poissonKernel_real_on_circle hR hz' (-t), poissonKernel_real_on_circle hR hz' t]
    nlinarith only [hb]

/-- `lem:two-point-kernel`. No boundary extension of the positive harmonic
function is assumed: the circle radius approaches 1 from below. -/
theorem two_point_harmonic {q : ℝ} (hq : 0 < q) (hqr : q < sharpRadius) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : ℂ → ℝ,
      HarmonicOnNhd U (ball (0 : ℂ) 1) →
      (∀ z ∈ ball (0 : ℂ) 1, 0 < U z) →
      ∀ t s : ℝ, 0 ≤ t → t ≤ q → |s| ≤ t →
        (1 + ε) * U (s : ℂ) ≤
          twoPointMinus t s * U ((-t : ℝ) : ℂ) + twoPointPlus t s * U (t : ℂ) := by
  obtain ⟨ε, hε, hkernel⟩ := twoPointKernel_uniform hq hqr
  refine ⟨ε, hε, ?_⟩
  intro U hU hpos t s ht htq hst
  have ht1 : |t| < 1 := by
    rw [abs_of_nonneg ht]
    exact htq.trans_lt (hqr.trans sharpRadius_lt_one)
  have hs1 : |s| < 1 := hst.trans_lt (htq.trans_lt (hqr.trans sharpRadius_lt_one))
  have hnt1 : |-t| < 1 := by simpa using ht1
  have hlim : ∀ a : ℝ, |a| < 1 →
      Tendsto (fun R : ℝ => U ((R * a : ℝ) : ℂ)) (𝓝[<] 1) (𝓝 (U (a : ℂ))) := by
    intro a ha
    have haD : (a : ℂ) ∈ ball (0 : ℂ) 1 := by
      simpa using scaled_real_mem_ball (by norm_num : (0 : ℝ) < 1) ha
    have hcont : ContinuousAt U (a : ℂ) := (hU _ haD).1.continuousAt
    have hcomp : ContinuousAt (fun R : ℝ => U ((R * a : ℝ) : ℂ)) 1 :=
      hcont.comp_of_eq (by fun_prop) (by simp)
    simpa only [one_mul] using hcomp.tendsto.mono_left
      (show (𝓝[<] (1 : ℝ)) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto ((hlim s hs1).const_mul (1 + ε))
    (((hlim (-t) hnt1).const_mul (twoPointMinus t s)).add
      ((hlim t ht1).const_mul (twoPointPlus t s)))
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with R hR
  have hUR : HarmonicContOnCl U (ball (0 : ℂ) R) := by
    apply HarmonicOnNhd.harmonicContOnCl
    rw [closure_ball _ hR.1.ne']
    exact hU.mono (closedBall_subset_ball hR.2)
  exact harmonic_two_point_on_closedBall hR.1 hUR
    (fun z hz => (hpos z (sphere_subset_ball hR.2 hz)).le)
    ht1 hs1 (hkernel t s · ht htq hst)

end ModifiedCartan
