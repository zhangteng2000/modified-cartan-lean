import ModifiedCartan.Harmonic
import ModifiedCartan.Basic
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

noncomputable section
set_option autoImplicit false
open Filter Topology Complex InnerProductSpace Metric Set Real
namespace ModifiedCartan

/-- Harmonicity under holomorphic changes of variable, proved using the library's
actual harmonic conjugate on the target disk. -/
theorem harmonic_comp_analytic_to_ball {u : ℂ → ℝ} {g : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (ball c R)) (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hmap : MapsTo g U (ball c R)) :
    HarmonicOnNhd (fun z => u (g z)) U := by
  obtain ⟨F, hF, he⟩ := hu.exists_analyticOnNhd_ball_re_eq
  intro z hz
  have hcomp := ((hF (g z) (hmap hz)).comp (hg z hz)).harmonicAt_re
  apply (harmonicAt_congr_nhds ?_).mp hcomp
  filter_upwards [hU.mem_nhds hz] with w hw
  exact he (hmap hw)

/-- Sharp centered Harnack inequalities for a nonnegative harmonic function on
an open disk, with no boundary-continuity assumption. -/
theorem harmonic_harnack_open {u : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hu : HarmonicOnNhd u (ball c R)) (hpos : ∀ z ∈ ball c R, 0 ≤ u z)
    (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * u c ≤ u w ∧
      u w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * u c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hwR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hevent : ∀ᶠ r in 𝓝[<] R,
      (r - ‖w - c‖) / (r + ‖w - c‖) * u c ≤ u w ∧
      u w ≤ (r + ‖w - c‖) / (r - ‖w - c‖) * u c := by
    filter_upwards [Ioo_mem_nhdsLT hwR] with r hr
    have hr0 : 0 < r := (norm_nonneg _).trans_lt hr.1
    have huc : HarmonicContOnCl u (ball c r) := by
      apply HarmonicOnNhd.harmonicContOnCl
      rw [closure_ball c hr0.ne']
      exact hu.mono (closedBall_subset_ball hr.2)
    exact harmonic_harnack_bounds huc (mem_ball_iff_norm.mpr hr.1)
      (fun z hz => hpos z (sphere_subset_ball hr.2 hz))
  have hcont1 : ContinuousAt (fun r : ℝ => (r - ‖w - c‖) / (r + ‖w - c‖) * u c) R := by
    apply ContinuousAt.mul _ continuousAt_const
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    positivity
  have hcont2 : ContinuousAt (fun r : ℝ => (r + ‖w - c‖) / (r - ‖w - c‖) * u c) R := by
    apply ContinuousAt.mul _ continuousAt_const
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    linarith
  constructor
  · exact le_of_tendsto (hcont1.tendsto.mono_left nhdsWithin_le_nhds) (hevent.mono (fun r hr => hr.1))
  · exact ge_of_tendsto (hcont2.tendsto.mono_left nhdsWithin_le_nhds) (hevent.mono (fun r hr => hr.2))

end ModifiedCartan
