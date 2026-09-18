import ModifiedCartan.FiniteFailurePoints
import ModifiedCartan.FailurePointsAvoidZeros
import ModifiedCartan.MovingPointLimits
import ModifiedCartan.ZeroFreeAnnulus

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- All failure points can be chosen in one fixed compact set disjoint from the
zeros of the limit. No connectedness of the open target is needed. -/
theorem zero_free_finite_failure_points {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → ℕ → ℂ → ℂ) {s : ℂ → ℂ} {U : Set ℂ}
    (hs : DifferentiableOn ℂ s (disk 1)) (hsne : ∃ z ∈ disk 1, s z ≠ 0)
    (hU : IsOpen U) (hU1 : U ⊆ disk 1)
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk 1))
    (hno : ∀ i, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence
      (fun n z => (A i (φ n) z)⁻¹) 0 U) :
    ∃ L : Set ℂ, IsCompact L ∧ L.Nonempty ∧ L ⊆ U ∧ (∀ z ∈ L, s z ≠ 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∃ z : ι → ℕ → ℂ, (∀ i n, z i n ∈ L) ∧
        ∀ᶠ n in atTop, ∀ i, Real.log ‖A i n (z i n)‖ ≤ C := by
  classical
  obtain ⟨K, hKU, hK, C, hC, hp⟩ := finite_unit_failure_points A hU
    (fun i n z hz => (hA i n).2 z (hU1 hz)) hno
  obtain ⟨L, hL, hLU, hLzero, hmove⟩ := compact_failure_points_avoid_zeros hs hsne hU hU1 hK hKU
  have hpL : ∀ᶠ n in atTop, ∀ i, ∃ z ∈ L, Real.log ‖A i n z‖ ≤ C := by
    filter_upwards [hp] with n hn i
    obtain ⟨z, hz, hbound⟩ := hn i
    obtain ⟨w, hw, hle⟩ := hmove (A i n) (hA i n) z hz
    exact ⟨w, hw, hle.trans hbound⟩
  obtain ⟨n₀, hn₀⟩ := hpL.exists
  obtain ⟨w₀, hw₀, _⟩ := hn₀ (Classical.arbitrary ι)
  have hchoose : ∀ i n, ∃ z ∈ L,
      (∀ j, ∃ w ∈ L, Real.log ‖A j n w‖ ≤ C) → Real.log ‖A i n z‖ ≤ C := by
    intro i n
    by_cases hn : ∀ j, ∃ w ∈ L, Real.log ‖A j n w‖ ≤ C
    · obtain ⟨z, hz, hbound⟩ := hn i
      exact ⟨z, hz, fun _ => hbound⟩
    · exact ⟨w₀, hw₀, fun h => False.elim (hn h)⟩
  choose z hz hbound using hchoose
  exact ⟨L, hL, ⟨w₀, hw₀⟩, hLU, hLzero, C, hC, z, hz,
    hpL.mono (fun n hn i => hbound i n hn)⟩

theorem complement_quotient_tendsto_one {a b : ℕ → ℂ} {c : ℝ}
    (hb : Tendsto b atTop (𝓝 0)) (hc : 0 < c)
    (hs : ∀ᶠ n in atTop, c ≤ ‖a n + b n‖) :
    Tendsto (fun n => a n / (a n + b n)) atTop (𝓝 1) := by
  have hq := quotient_tendsto_zero_of_norm_lower hb hc hs
  have ht : Tendsto (fun n => 1 - b n / (a n + b n)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hq
  apply ht.congr'
  filter_upwards [hs] with n hn
  have hnz : a n + b n ≠ 0 := norm_pos_iff.mp (hc.trans_le hn)
  field_simp
  ring

/-- Endpoint ratios forced by the two failure-point bounds. -/
theorem two_term_failure_limits {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ}
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk 1))
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) 0 (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    {L : Set ℂ} (hL : IsCompact L) (hL1 : L ⊆ disk 1) (hsne : ∀ z ∈ L, s z ≠ 0)
    {z : Fin 2 → ℕ → ℂ} (hz : ∀ i n, z i n ∈ L) {C : ℝ}
    (hlog : ∀ᶠ n in atTop, ∀ i, Real.log ‖A i n (z i n)‖ ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ n in atTop, ∀ w ∈ L, c ≤ ‖∑ i, a i n w‖) ∧
      (∀ i, Tendsto (fun n => a i n (z i n)) atTop (𝓝 0)) ∧
      Tendsto (fun n => a 0 n (z 0 n) / (∑ i, a i n (z 0 n))) atTop (𝓝 0) ∧
      Tendsto (fun n => a 0 n (z 1 n) / (∑ i, a i n (z 1 n))) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop, c / 2 ≤ ‖a 1 n (z 0 n)‖ ∧ c / 2 ≤ ‖a 0 n (z 1 n)‖ := by
  have hs := compactConvergence_holomorphic isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
  obtain ⟨c, hc, hlow⟩ := compactConvergence_eventually_lower_bound hsum hL1 hL
    (hs.continuousOn.mono hL1) hsne
  have hvan : ∀ i, Tendsto (fun n => a i n (z i n)) atTop (𝓝 0) := by
    intro i
    apply tendsto_zero_of_small_ratio_bounded_log (A := fun n => A i n (z i n))
      (compactConvergence_eval_zero (f := fun n w => a i n w / A i n w) (z := z i)
        (hsmall i) hL1 hL (Eventually.of_forall (hz i)))
    exact hlog.mono (fun n hn => ⟨(hA i n).2 _ (hL1 (hz i n)), hn i⟩)
  have hlowi : ∀ i, ∀ᶠ n in atTop, c ≤ ‖∑ j, a j n (z i n)‖ := fun i =>
    hlow.mono (fun n hn => hn _ (hz i n))
  refine ⟨c, hc, hlow, hvan,
    quotient_tendsto_zero_of_norm_lower (hvan 0) hc (hlowi 0), ?_, ?_⟩
  · simpa only [Fin.sum_univ_two] using
      complement_quotient_tendsto_one (a := fun n => a 0 n (z 1 n)) (hvan 1) hc
        (by simpa only [Fin.sum_univ_two] using hlowi 1)
  · have hsmall₀ : ∀ᶠ n in atTop, ‖a 0 n (z 0 n)‖ < c / 2 := by
      exact (hvan 0).norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using half_pos hc))
    have hsmall₁ : ∀ᶠ n in atTop, ‖a 1 n (z 1 n)‖ < c / 2 := by
      exact (hvan 1).norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using half_pos hc))
    filter_upwards [hlowi 0, hlowi 1, hsmall₀, hsmall₁] with n hn₀ hn₁ h₀ h₁
    simp only [Fin.sum_univ_two] at hn₀ hn₁
    constructor
    · linarith [norm_add_le (a 0 n (z 0 n)) (a 1 n (z 0 n))]
    · linarith [norm_add_le (a 0 n (z 1 n)) (a 1 n (z 1 n))]

end ModifiedCartan
