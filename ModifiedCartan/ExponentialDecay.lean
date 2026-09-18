import ModifiedCartan.NegligibleDerivatives
import ModifiedCartan.Convergence

noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics Metric Set
namespace ModifiedCartan

theorem exp_negative_growth_tendsto_zero {M e : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hM : Tendsto M atTop atTop) (he : e =o[atTop] M) (C k : ℝ) :
    Tendsto (fun n => Real.exp (-c * M n + C + k * e n)) atTop (𝓝 0) := by
  have herror : (fun n => C + k * e n) =o[atTop] M :=
    ((isLittleO_const_id_atTop C).comp_tendsto hM).add (he.const_mul_left k)
  have hlimit : Tendsto (fun n => Real.exp (-(c / 2) * M n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hM.const_mul_atTop_of_neg (neg_lt_zero.mpr (half_pos hc)))
  apply squeeze_zero' (Eventually.of_forall (fun n => (Real.exp_pos _).le)) ?_ hlimit
  filter_upwards [herror.bound (half_pos hc), hM.eventually (eventually_ge_atTop (0 : ℝ))] with n hn hMn
  apply Real.exp_le_exp.mpr
  have hbound : C + k * e n ≤ (c / 2) * M n := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, abs_of_nonneg hMn] using hn
  linarith

theorem uniform_zero_of_exp_negative_growth {f : ℕ → ℂ → ℂ} {U : Set ℂ}
    {M e : ℕ → ℝ} {c C k : ℝ}
    (hc : 0 < c) (hM : Tendsto M atTop atTop) (he : e =o[atTop] M)
    (hf : ∀ᶠ n in atTop, ∀ z ∈ U, ‖f n z‖ ≤ Real.exp (-c * M n + C + k * e n)) :
    TendstoUniformlyOn f 0 atTop U := by
  have hlimit := exp_negative_growth_tendsto_zero hc hM he C k
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hf, hlimit.eventually (gt_mem_nhds hε)] with n hn hεn
  intro z hz
  simpa only [Pi.zero_apply, dist_zero_left] using (hn z hz).trans_lt hεn

end ModifiedCartan
