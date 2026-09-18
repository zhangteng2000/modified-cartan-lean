import ModifiedCartan.LogarithmicPoles

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Metric Set
namespace ModifiedCartan

def reflectedPole (S : ℝ) (a z : ℂ) : ℂ :=
  conj a / (((S ^ 2 : ℝ) : ℂ) - conj a * z)

theorem reflectedPole_analytic {S : ℝ} (hS : 0 < S) {a : ℂ} (ha : ‖a‖ < S) :
    AnalyticOnNhd ℂ (reflectedPole S a) (closedBall (0 : ℂ) S) := by
  intro z hz
  exact analyticAt_const.div (by fun_prop) (blaschke_numerator_ne_zero hS ha (by simpa using hz))

theorem reflectedPole_iteratedDeriv_bound {S r : ℝ} (hr : 0 ≤ r) (hrS : r < S)
    {a z : ℂ} (ha : ‖a‖ < S) (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖iteratedDeriv n (reflectedPole S a) z‖ ≤
      (n.factorial : ℝ) * (2 / (S - r)) / ((S - r) / 2) ^ n := by
  have hS : 0 < S := hr.trans_lt hrS
  let δ := (S - r) / 2
  let B := (S + r) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hBS : B < S := by dsimp [B]; linarith
  have hsub : closedBall z δ ⊆ closedBall (0 : ℂ) B := by
    intro w hw
    have hd : ‖w - z‖ ≤ δ := by simpa [mem_closedBall, dist_eq_norm] using hw
    have hh := norm_add_le (w - z) z
    rw [sub_add_cancel] at hh
    have he : ‖w‖ ≤ B := by dsimp [δ, B] at *; linarith
    simpa using he
  have hfb : ∀ w ∈ closedBall (0 : ℂ) B, ‖reflectedPole S a w‖ ≤ 2 / (S - r) := by
    intro w hw
    have hh := reflected_pole_norm_bound hS hB hBS ha (by simpa using hw)
    have he : 1 / (S - B) = 2 / (S - r) := by dsimp [B]; field_simp; ring
    rwa [he] at hh
  have hf : DifferentiableOn ℂ (reflectedPole S a) (closure (ball z δ)) := by
    rw [closure_ball _ hδ.ne']
    exact (reflectedPole_analytic hS ha).differentiableOn.mono
      (hsub.trans (closedBall_subset_closedBall hBS.le))
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hδ hf.diffContOnCl
    (fun w hw => hfb w (hsub (sphere_subset_closedBall hw)))

theorem blaschke_logDeriv_iterated_bound {S r : ℝ} (hr : 0 ≤ r) (hrS : r < S)
    {a z : ℂ} (ha : ‖a‖ < S) (hz : ‖z‖ ≤ r) (hza : z ≠ a) (n : ℕ) :
    ‖iteratedDeriv n (logDeriv (blaschkeFactor S a)) z‖ ≤
      (n.factorial : ℝ) * ‖z - a‖ ^ (-1 - (n : ℤ)) +
      (n.factorial : ℝ) * (2 / (S - r)) / ((S - r) / 2) ^ n := by
  have hS : 0 < S := hr.trans_lt hrS
  have hzS : z ∈ ball (0 : ℂ) S := by simpa using hz.trans_lt hrS
  have he : logDeriv (blaschkeFactor S a) =ᶠ[nhds z]
      (fun w => 1 / (w - a) + reflectedPole S a w) := by
    filter_upwards [isOpen_ball.mem_nhds hzS,
      (isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({a} : Set ℂ)ᶜ from hza))] with w hw hwa
    exact logDeriv_blaschkeFactor hS ha (show ‖w‖ ≤ S from (by simpa using hw : ‖w‖ < S).le) hwa
  rw [he.iteratedDeriv_eq n]
  have hfirst : AnalyticAt ℂ (fun w => 1 / (w - a)) z :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)
  have hsecond := reflectedPole_analytic hS ha z (ball_subset_closedBall hzS)
  rw [iteratedDeriv_fun_add hfirst.contDiffAt hsecond.contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_iteratedDeriv_reciprocal_shift n a z).le
    (reflectedPole_iteratedDeriv_bound hr hrS ha hz n))

end ModifiedCartan
