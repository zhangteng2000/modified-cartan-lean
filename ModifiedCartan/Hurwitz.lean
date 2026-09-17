import ModifiedCartan.Convergence
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Field.Lemmas

noncomputable section
set_option autoImplicit false
open Filter Topology Metric
namespace ModifiedCartan

/-- Hurwitz's nonvanishing conclusion, with connectedness confined to this theorem.
The proof uses isolated zeros and the maximum principle for reciprocals. -/
theorem hurwitz_nonvanishing {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hg : ∀ n, IsHolomorphicUnit (g n) U) (hlim : CompactConvergence g h U)
    (hnotzero : ∃ z ∈ U, h z ≠ 0) : ∀ z ∈ U, h z ≠ 0 := by
  have hh := compactConvergence_holomorphic hU hlim (fun n => (hg n).1)
  have ha : AnalyticOnNhd ℂ h U := hh.analyticOnNhd hU
  intro w hw hzero
  have hpunctured : ∀ᶠ z in 𝓝[≠] w, h z ≠ 0 := by
    rcases (ha w hw).eventually_eq_zero_or_eventually_ne_zero with hz | hn
    · have hall := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hw hz
      obtain ⟨z, hzU, hzn⟩ := hnotzero
      exact False.elim (hzn (hall hzU))
    · exact hn
  have hgood : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ≠ w → h z ≠ 0) := by
    filter_upwards [hU.mem_nhds hw, eventually_nhdsWithin_iff.mp hpunctured] with z hz hne
    exact ⟨hz, hne⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hgood
  let ρ := r / 2
  have hρ : 0 < ρ := half_pos hr
  have hρr : ρ < r := half_lt_self hr
  have hCU : closedBall w ρ ⊆ U := fun z hz => (hrsub (closedBall_subset_ball hρr hz)).1
  have hSU : sphere w ρ ⊆ U := sphere_subset_closedBall.trans hCU
  have hSnz : ∀ z ∈ sphere w ρ, h z ≠ 0 := by
    intro z hz
    apply (hrsub (sphere_subset_ball hρr hz)).2
    intro heq
    subst z
    have he : (0 : ℝ) = ρ := by simpa using hz
    linarith
  obtain ⟨c, hc, hcb⟩ := (isCompact_sphere w ρ).exists_forall_le'
    ((hh.continuousOn.mono hSU).norm) (fun z hz => norm_pos_iff.mpr (hSnz z hz))
  have hunif := hlim (sphere w ρ) hSU (isCompact_sphere w ρ)
  have hbound : ∀ᶠ n in atTop, c / 2 ≤ ‖g n w‖ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif (c / 2) (half_pos hc)] with n hn
    have hcircle : ∀ z ∈ sphere w ρ, c / 2 ≤ ‖g n z‖ := by
      intro z hz
      have hdist : ‖h z - g n z‖ < c / 2 := by simpa [dist_eq_norm] using hn z hz
      have hnorm : ‖h z‖ ≤ ‖g n z‖ + ‖h z - g n z‖ := by
        calc
          _ = ‖g n z + (h z - g n z)‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      linarith [hcb z hz]
    have hdinv : DifferentiableOn ℂ (fun z => (g n z)⁻¹) (closure (ball w ρ)) := by
      rw [closure_ball w hρ.ne']
      exact ((hg n).1.mono hCU).inv (fun z hz => (hg n).2 z (hCU hz))
    have hinv : ‖(g n w)⁻¹‖ ≤ (c / 2)⁻¹ := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdinv.diffContOnCl
        (fun z hz => ?_) (subset_closure (mem_ball_self hρ))
      rw [frontier_ball w hρ.ne'] at hz
      rw [norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr ((hg n).2 z (hSU hz))) (half_pos hc)).mpr (hcircle z hz)
    rw [norm_inv] at hinv
    exact (inv_le_inv₀ (norm_pos_iff.mpr ((hg n).2 w hw)) (half_pos hc)).mp hinv
  have hnormlim := (compactConvergence_pointwise hlim hw).norm
  have hle := ge_of_tendsto hnormlim hbound
  rw [hzero, norm_zero] at hle
  linarith

theorem compactConvergence_inv {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hlim : CompactConvergence g h U) (hh : ContinuousOn h U)
    (hne : ∀ z ∈ U, h z ≠ 0) :
    CompactConvergence (fun n z => (g n z)⁻¹) (fun z => (h z)⁻¹) U :=
  (compactConvergence_iff hU).mpr (((compactConvergence_iff hU).mp hlim).inv₀ hh hne)

theorem hurwitz_reciprocal_locallyBounded {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hg : ∀ n, IsHolomorphicUnit (g n) U) (hlim : CompactConvergence g h U)
    (hnotzero : ∃ z ∈ U, h z ≠ 0) : LocallyBounded (fun n z => (g n z)⁻¹) U := by
  have hh := compactConvergence_holomorphic hU hlim (fun n => (hg n).1)
  exact compactConvergence_locallyBounded
    (compactConvergence_inv hU hlim hh.continuousOn (hurwitz_nonvanishing hU hconn hg hlim hnotzero))
    (fun n => (hg n).1.continuousOn.inv₀ (hg n).2)

/-- Once the bounded normalized quotients have limits, connectedness and Hurwitz
give two distinct dominant indices. Montel extraction is a separate obligation. -/
theorem cclass_two_dominants_of_quotient_limits {p : ℕ} {f : Family p}
    {I : Finset (Fin p)} {U : Set ℂ} {k : Fin p} {H : Fin p → ℂ → ℂ}
    (hU : IsOpen U) (hconn : IsConnected U)
    (hf : ∀ i n, IsHolomorphicUnit (f i n) U) (hk : IsDominant f I U k)
    (hlimits : ∀ j ∈ I, CompactConvergence (fun n z => f j n z / f k n z) (H j) U) :
    ∃ l : Fin p, l ≠ k ∧ IsDominant f I U l := by
  classical
  obtain ⟨z, hz⟩ := hconn.nonempty
  have hsum : ∑ j ∈ I, H j z = 0 :=
    tendsto_nhds_unique
      (tendsto_finsetSum I (fun j hj => compactConvergence_pointwise (hlimits j hj) hz))
      (compactConvergence_pointwise hk.2.2 hz)
  have hk1 : H k z = 1 := by
    have ht := compactConvergence_pointwise (hlimits k hk.1) hz
    have he : (fun n => f k n z / f k n z) = fun _ => (1 : ℂ) := by
      funext n
      exact div_self ((hf k n).2 z hz)
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hex : ∃ l ∈ I, l ≠ k ∧ H l z ≠ 0 := by
    by_contra hn
    push Not at hn
    have he : ∑ j ∈ I, H j z = H k z := by
      apply Finset.sum_eq_single k
      · intro j hj hjk
        exact hn j hj hjk
      · exact fun h => False.elim (h hk.1)
    rw [he, hk1] at hsum
    exact one_ne_zero hsum
  obtain ⟨l, hl, hlk, hlnz⟩ := hex
  have hunits : ∀ n, IsHolomorphicUnit (fun z => f l n z / f k n z) U := by
    intro n
    exact ⟨(hf l n).1.div (hf k n).1 (hf k n).2,
      fun z hz => div_ne_zero ((hf l n).2 z hz) ((hf k n).2 z hz)⟩
  have hbound := hurwitz_reciprocal_locallyBounded hU hconn.isPreconnected hunits
    (hlimits l hl) ⟨z, hz, hlnz⟩
  have hreverse : LocallyBounded (fun n z => f k n z / f l n z) U := by
    simpa only [inv_div] using hbound
  exact ⟨l, hlk, dominant_change_index (fun i n => (hf i n).2) hk hl hreverse⟩

end ModifiedCartan
