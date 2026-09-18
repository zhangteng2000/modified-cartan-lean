import ModifiedCartan.Hurwitz
import ModifiedCartan.Statements

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- Around every point, a nontrivial holomorphic function is bounded away from
zero on some surrounding circle, including when the center is a zero. -/
theorem nonzero_surrounding_circle {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hh : DifferentiableOn ℂ h U)
    (hne : ∃ z ∈ U, h z ≠ 0) {w : ℂ} (hw : w ∈ U) :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ closedBall w ρ ⊆ U ∧
      ∀ z ∈ sphere w ρ, c ≤ ‖h z‖ := by
  have ha := hh.analyticOnNhd hU
  have hp : ∀ᶠ z in 𝓝[≠] w, h z ≠ 0 := by
    rcases (ha w hw).eventually_eq_zero_or_eventually_ne_zero with hz | hn
    · have hall := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hw hz
      obtain ⟨z, hzU, hzn⟩ := hne
      exact False.elim (hzn (hall hzU))
    · exact hn
  have hgood : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ≠ w → h z ≠ 0) := by
    filter_upwards [hU.mem_nhds hw, eventually_nhdsWithin_iff.mp hp] with z hz hnz
    exact ⟨hz, hnz⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hgood
  have hcU : closedBall w (r / 2) ⊆ U := fun z hz =>
    (hsub (closedBall_subset_ball (half_lt_self hr) hz)).1
  have hsU := sphere_subset_closedBall.trans hcU
  have hsne : ∀ z ∈ sphere w (r / 2), h z ≠ 0 := by
    intro z hz
    apply (hsub (sphere_subset_ball (half_lt_self hr) hz)).2
    intro he
    subst z
    have : (0 : ℝ) = r / 2 := by simpa using hz
    linarith
  obtain ⟨c, hc, hcb⟩ := (isCompact_sphere w (r / 2)).exists_forall_le'
    (hh.continuousOn.mono hsU).norm (fun z hz => norm_pos_iff.mpr (hsne z hz))
  exact ⟨r / 2, c, half_pos hr, hc, hcU, hcb⟩

/-- Holomorphic cancellation across the zeros of a nontrivial limit.
The maximum principle upgrades division on surrounding circles to local uniform convergence. -/
theorem compactConvergence_cancel_nontrivial {a g : ℕ → ℂ → ℂ} {s : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (ha : ∀ n, DifferentiableOn ℂ (a n) U) (hg : ∀ n, DifferentiableOn ℂ (g n) U)
    (halim : CompactConvergence a s U)
    (hprod : CompactConvergence (fun n z => a n z * g n z) (fun _ => 0) U)
    (hsne : ∃ z ∈ U, s z ≠ 0) : CompactConvergence g (fun _ => 0) U := by
  have hs := compactConvergence_holomorphic hU halim ha
  apply (compactConvergence_iff hU).mpr
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro w hw
  obtain ⟨ρ, c, hρ, hc, hCU, hcb⟩ := nonzero_surrounding_circle hU hconn hs hsne hw
  have hSU := sphere_subset_closedBall.trans hCU
  refine ⟨ball w ρ, nhdsWithin_le_nhds (ball_mem_nhds w hρ), ?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h1 := Metric.tendstoUniformlyOn_iff.mp
    (halim (sphere w ρ) hSU (isCompact_sphere w ρ)) (c / 2) (half_pos hc)
  have h2 := Metric.tendstoUniformlyOn_iff.mp
    (hprod (sphere w ρ) hSU (isCompact_sphere w ρ)) (c * ε / 4) (by positivity)
  filter_upwards [h1, h2] with n hn hnprod
  have hcircle : ∀ z ∈ sphere w ρ, ‖g n z‖ ≤ ε / 2 := by
    intro z hz
    have hdist : ‖s z - a n z‖ < c / 2 := by simpa [dist_eq_norm] using hn z hz
    have htriangle : ‖s z‖ ≤ ‖a n z‖ + ‖s z - a n z‖ := by
      calc
        _ = ‖a n z + (s z - a n z)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have halower : c / 2 ≤ ‖a n z‖ := by linarith [hcb z hz]
    have hproduct : ‖a n z‖ * ‖g n z‖ < c * ε / 4 := by
      simpa only [dist_zero_left, norm_mul] using hnprod z hz
    nlinarith [norm_nonneg (g n z)]
  have hgd : DifferentiableOn ℂ (g n) (closure (ball w ρ)) := by
    rw [closure_ball w hρ.ne']
    exact (hg n).mono hCU
  intro z hz
  have hbound : ‖g n z‖ ≤ ε / 2 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgd.diffContOnCl
      (fun y hy => ?_) (subset_closure hz)
    rw [frontier_ball w hρ.ne'] at hy
    exact hcircle y hy
  simpa only [dist_zero_left] using hbound.trans_lt (half_lt_self hε)

/-- The exact m = 1 case of the manuscript absorption theorem, on the entire unit disk. -/
theorem absorption_one : AbsorptionAt 1 (disk 1) := by
  intro A a s hA ha hsmall hsum hsne
  have hlim : CompactConvergence (a 0) s (disk 1) := by
    simpa only [Fin.sum_univ_one] using hsum
  have hinv : ∀ n, DifferentiableOn ℂ (fun z => (A 0 n z)⁻¹) (disk 1) :=
    fun n => (hA 0 n).1.inv (hA 0 n).2
  have hprod : CompactConvergence (fun n z => a 0 n z * (A 0 n z)⁻¹) (fun _ => 0) (disk 1) := by
    simpa only [div_eq_mul_inv] using hsmall 0
  have hconv := compactConvergence_cancel_nontrivial isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected (ha 0) hinv hlim hprod hsne
  exact ⟨0, id, strictMono_id, hconv⟩

end ModifiedCartan
