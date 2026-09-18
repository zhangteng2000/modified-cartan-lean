import ModifiedCartan.CircleExceptional
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
set_option autoImplicit false
open Filter Metric Set Real
namespace ModifiedCartan

theorem meromorphicOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (n : ℕ) : MeromorphicOn (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem proximityMean_mul_le {f g : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (sphere (0 : ℂ) |R|))
    (hg : MeromorphicOn g (sphere (0 : ℂ) |R|)) :
    proximityMean (fun z => f z * g z) R ≤ proximityMean f R + proximityMean g R := by
  simp only [proximityMean, ValueDistribution.proximity_top]
  apply (Real.circleAverage_mono (hf.mul hg).circleIntegrable_posLog_norm
    (hf.circleIntegrable_posLog_norm.add hg.circleIntegrable_posLog_norm)
    (fun z _ => by simpa only [Pi.mul_apply, Pi.add_apply, norm_mul] using (Real.posLog_mul (x := ‖f z‖) (y := ‖g z‖)))).trans_eq
  exact Real.circleAverage_add hf.circleIntegrable_posLog_norm hg.circleIntegrable_posLog_norm

theorem proximityMean_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {R : ℝ}
    (hf : ∀ i ∈ s, MeromorphicOn (f i) (sphere (0 : ℂ) |R|)) :
    proximityMean (fun z => ∑ i ∈ s, f i z) R ≤
      ∑ i ∈ s, proximityMean (f i) R + Real.log s.card := by
  simp only [proximityMean, ValueDistribution.proximity_top]
  have hi := fun i h => (hf i h).circleIntegrable_posLog_norm
  have hsum : MeromorphicOn (fun z => ∑ i ∈ s, f i z) (sphere (0 : ℂ) |R|) := by
    intro z hz
    exact MeromorphicAt.fun_sum (fun i h => hf i h z hz)
  have hb : CircleIntegrable ((∑ i ∈ s, fun z => Real.posLog ‖f i z‖) + fun _ => Real.log s.card) 0 R :=
    (CircleIntegrable.sum s hi).add (circleIntegrable_const _ _ _)
  have hle := Real.circleAverage_mono hsum.circleIntegrable_posLog_norm hb
    (fun z _ => by simpa only [Pi.add_apply, Finset.sum_apply, add_comm] using
      (Real.posLog_norm_sum_le s (fun i => f i z)))
  apply hle.trans_eq
  rw [Real.circleAverage_add (CircleIntegrable.sum s hi) (circleIntegrable_const _ _ _),
    Real.circleAverage_sum hi, Real.circleAverage_const]

theorem proximityMean_const_mul_le (a : ℂ) {f : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (sphere (0 : ℂ) |R|)) :
    proximityMean (fun z => a * f z) R ≤ Real.posLog ‖a‖ + proximityMean f R := by
  have hconst : MeromorphicOn (fun _ : ℂ => a) (sphere (0 : ℂ) |R|) := fun _ _ => analyticAt_const.meromorphicAt
  simpa [proximityMean, ValueDistribution.proximity_const] using proximityMean_mul_le hconst hf

theorem proximityMean_congr_codiscrete {f g : ℂ → ℂ} {R : ℝ} (hR : R ≠ 0)
    (hf : MeromorphicOn f (sphere (0 : ℂ) |R|))
    (hg : MeromorphicOn g (sphere (0 : ℂ) |R|))
    (he : f =ᶠ[codiscreteWithin (sphere (0 : ℂ) |R|)] g) :
    proximityMean f R = proximityMean g R := by
  simp only [proximityMean, ValueDistribution.proximity_top]
  apply le_antisymm
  · apply circleAverage_mono_codiscrete hR hf.circleIntegrable_posLog_norm hg.circleIntegrable_posLog_norm
    filter_upwards [he] with z hz
    exact le_of_eq (congrArg (fun w : ℂ => Real.posLog ‖w‖) hz)
  · apply circleAverage_mono_codiscrete hR hg.circleIntegrable_posLog_norm hf.circleIntegrable_posLog_norm
    filter_upwards [he] with z hz
    exact le_of_eq (congrArg (fun w : ℂ => Real.posLog ‖w‖) hz.symm)

end ModifiedCartan
