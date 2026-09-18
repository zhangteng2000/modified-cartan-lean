import ModifiedCartan.AnalyticStatements
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic

noncomputable section
set_option autoImplicit false
open Filter Metric Set MeasureTheory Real
namespace ModifiedCartan

theorem circle_codiscrete_ae {P : ℂ → Prop} {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hP : ∀ᶠ z in codiscreteWithin (sphere c |R|), P z) :
    ∀ᵐ θ : ℝ ∂volume.restrict (uIoc 0 (2 * Real.pi)), P (circleMap c R θ) := by
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  exact codiscreteWithin_mono (by simp only [Set.subset_univ]) (circleMap_preimage_codiscrete hR hP)

theorem circleAverage_mono_codiscrete {f g : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R)
    (hfg : ∀ᶠ z in codiscreteWithin (sphere c |R|), f z ≤ g z) :
    Real.circleAverage f c R ≤ Real.circleAverage g c R := by
  unfold Real.circleAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_ae_restrict (by positivity) hf hg
  have hh := circle_codiscrete_ae hR hfg
  rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), restrict_Ioc_eq_restrict_Icc] at hh
  filter_upwards [hh] with θ hθ
  exact hθ

theorem meromorphic_circle_norm_rpow_measurable {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : MeromorphicOn f (sphere c |R|)) (p : ℝ) :
    Measurable (fun θ : ℝ => ‖f (circleMap c R θ)‖ ^ p) := by
  have hcomp : Meromorphic (fun θ : ℝ => f (circleMap c R θ)) := by
    intro θ
    exact (hf _ (circleMap_mem_sphere' c R θ)).comp_analyticAt
      (analyticOnNhd_circleMap c R θ (mem_univ θ))
  exact hcomp.measurable.norm.pow_const p

theorem circleIntegrable_norm_rpow_of_codiscrete_le {f : ℂ → ℂ} {g : ℂ → ℝ}
    {c : ℂ} {R p : ℝ} (hR : R ≠ 0) (hf : MeromorphicOn f (sphere c |R|))
    (hg : CircleIntegrable g c R)
    (hfg : ∀ᶠ z in codiscreteWithin (sphere c |R|), ‖f z‖ ^ p ≤ g z) :
    CircleIntegrable (fun z => ‖f z‖ ^ p) c R := by
  apply hg.mono_fun' (meromorphic_circle_norm_rpow_measurable hf p).aestronglyMeasurable
  filter_upwards [circle_codiscrete_ae hR hfg] with θ hθ
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hθ

end ModifiedCartan
