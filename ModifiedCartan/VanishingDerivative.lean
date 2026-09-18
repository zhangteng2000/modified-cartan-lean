import ModifiedCartan.MovingPointLimits
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.Clopen

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

def LocallyVanishingDerivative (f : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, (∀ z ∈ K, DifferentiableAt ℂ (f n) z) ∧ ∀ z ∈ K, ‖deriv (f n) z‖ ≤ ε

theorem vanishingDerivative_closedBall {f : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyVanishingDerivative f U) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hball : closedBall c r ⊆ U) {z : ℕ → ℂ}
    (hz : ∀ᶠ n in atTop, z n ∈ closedBall c r) :
    Tendsto (fun n => f n (z n) - f n c) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < r + 1 := by linarith
  filter_upwards [hf (closedBall c r) hball (isCompact_closedBall c r)
    (ε / (r + 1)) (div_pos hε hden), hz] with n hn hzn
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le hn.1 hn.2 (convex_closedBall c r)
    (mem_closedBall_self hr) hzn
  have hdist : ‖z n - c‖ ≤ r := mem_closedBall_iff_norm.mp hzn
  have hless : (ε / (r + 1)) * r < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  simpa only [dist_zero_right] using hb.trans_lt
    ((mul_le_mul_of_nonneg_left hdist (div_pos hε hden).le).trans_lt hless)

theorem vanishingDerivative_moving_center {f : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyVanishingDerivative f U) (hU : IsOpen U) {c : ℂ} (hc : c ∈ U)
    {z : ℕ → ℂ} (hz : Tendsto z atTop (𝓝 c)) :
    Tendsto (fun n => f n (z n) - f n c) atTop (𝓝 0) := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU c hc
  apply vanishingDerivative_closedBall hf (half_pos hr).le
    ((closedBall_subset_ball (half_lt_self hr)).trans hrU)
  exact (hz.eventually (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))).mono
    (fun _ h => ball_subset_closedBall h)

/-- Derivatives tending locally uniformly to zero force differences between
any two fixed points to tend to zero on a connected open domain. -/
theorem vanishingDerivative_fixed_difference {f : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyVanishingDerivative f U) (hU : IsOpen U) (hconn : IsPreconnected U)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    Tendsto (fun n => f n y - f n x) atTop (𝓝 0) := by
  apply hconn.induction₂ (fun x y => Tendsto (fun n => f n y - f n x) atTop (𝓝 0)) ?_ ?_ ?_ hx hy
  · intro x hx
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
    have hn : ∀ᶠ y in 𝓝 x, y ∈ ball x (r / 2) := isOpen_ball.mem_nhds (mem_ball_self (half_pos hr))
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
    exact vanishingDerivative_closedBall hf (half_pos hr).le
      ((closedBall_subset_ball (half_lt_self hr)).trans hrU)
      (Eventually.of_forall (fun _ => ball_subset_closedBall hy))
  · intro x y z _ _ _ hxy hyz
    have h := hyz.add hxy
    simpa only [add_zero, sub_add_sub_cancel] using h
  · intro x y _ _ hxy
    simpa only [neg_zero, neg_sub] using hxy.neg

theorem vanishingDerivative_moving_difference {f : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyVanishingDerivative f U) (hU : IsOpen U) (hconn : IsPreconnected U)
    {x y : ℕ → ℂ} {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U)
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b)) :
    Tendsto (fun n => f n (y n) - f n (x n)) atTop (𝓝 0) := by
  have hleft := vanishingDerivative_moving_center hf hU ha hx
  have hright := vanishingDerivative_moving_center hf hU hb hy
  have hfixed := vanishingDerivative_fixed_difference hf hU hconn ha hb
  have h := (hright.add hfixed).sub hleft
  simpa only [add_zero, sub_zero, sub_add_sub_cancel, sub_sub_sub_cancel_right] using h

end ModifiedCartan
