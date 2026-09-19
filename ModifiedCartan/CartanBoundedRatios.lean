import ModifiedCartan.CartanBoundedPairs
import ModifiedCartan.QuotientGrowth
import ModifiedCartan.ProximityGrowth
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

theorem unit_montel_limit_of_no_zero {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hg : ∀ n, IsHolomorphicUnit (g n) U)
    (hb : LocallyBounded g U)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence (fun n => g (φ n)) (fun _ => 0) U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ,
      IsHolomorphicUnit G U ∧ CompactConvergence (fun n => g (φ n)) G U := by
  obtain ⟨φ,hφ,G,hG,hlim⟩ := montel_subsequence hU (fun n => (hg n).1) hb
  have hnG : ∃ z ∈ U, G z ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hno
    exact ⟨φ,hφ,(compactConvergence_iff hU).mpr
      (((compactConvergence_iff hU).mp hlim).congr_right hn)⟩
  exact ⟨φ,hφ,G,⟨hG,hurwitz_nonvanishing hU hconn (fun n => hg (φ n)) hlim hnG⟩,hlim⟩

theorem ratio_neg_one_of_locallyBounded {p : ℕ} {f : Family p} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : ∀ i n, IsHolomorphicUnit (f i n) U)
    (hno : NoVanishingQuotientSubsequence f U) (hfinite : OnlyNegativeOneUnitLimits f U)
    {i j : Fin p} (hij : i ≠ j) (hb : LocallyBounded (fun n z => f i n z/f j n z) U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => f i (φ n) z/f j (φ n) z) (fun _ => -1) U := by
  obtain ⟨φ,hφ,G,hG,hlim⟩ := unit_montel_limit_of_no_zero hU hconn
    (fun n => unit_quotient (hf i n) (hf j n)) hb (hno i j)
  exact ⟨φ,hφ,(compactConvergence_iff hU).mpr
    (((compactConvergence_iff hU).mp hlim).congr_right (hfinite i j hij φ hφ G hG hlim))⟩

/-- After the vanishing and finite non-minus-one cases are excluded,
two locally bounded quotients along three distinct indices are impossible. -/
theorem no_locallyBounded_three_chain {p : ℕ} {f : Family p} {U : Set ℂ}
    (hne : U.Nonempty) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : ∀ i n, IsHolomorphicUnit (f i n) U)
    (hno : NoVanishingQuotientSubsequence f U) (hfinite : OnlyNegativeOneUnitLimits f U)
    {a b c : Fin p} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : LocallyBounded (fun n z => f a n z/f b n z) U)
    (h2 : LocallyBounded (fun n z => f b n z/f c n z) U) : False := by
  obtain ⟨φ,hφ,hlim1⟩ := ratio_neg_one_of_locallyBounded hU hconn hf hno hfinite hab h1
  obtain ⟨ψ,hψ,hlim2⟩ := ratio_neg_one_of_locallyBounded hU hconn
    (fun i n => hf i (φ n)) (noVanishingQuotientSubsequence_subsequence hno hφ)
    (onlyNegativeOneUnitLimits_subsequence hfinite hφ) hbc (locallyBounded_subsequence h2 φ)
  have hone := ratio_one_of_overlapping_cancellations hU (fun i n => hf i (φ (ψ n)))
    (compactConvergence_subsequence hlim1 hψ) hlim2
  obtain ⟨w,hw⟩ := hne
  have hbad := hfinite a c hac (φ ∘ ψ) (hφ.comp hψ) (fun _ => 1)
    ⟨differentiableOn_const 1,fun _ _ => one_ne_zero⟩ hone w hw
  norm_num at hbad

theorem locallyBounded_quotients_of_pairGrowth_at_radius {p : ℕ} {f : Family p} {R C : ℝ}
    (hR : 0 < R) (hR1 : R < 1) (hf : UnitFamily f)
    (hb : ∀ n, pairGrowthMean (fun i => f i n) R ≤ C) :
    ∀ i j, LocallyBounded (fun n z => f i n z/f j n z) (disk R) := by
  intro i j K hK hcK
  obtain ⟨a,⟨ha,haR⟩,hKa⟩ := exists_pos_lt_subset_ball hR hcK.isClosed hK
  let Q := (R+a)/(R-a)
  have hQ : 0 ≤ Q := div_nonneg (by linarith) (by linarith)
  refine ⟨Real.exp (Q*C),?_⟩
  intro n z hz
  have hqu := unit_quotient (hf i n) (hf j n)
  have hza : ‖z‖ ≤ a := (by simpa using hKa hz : ‖z‖ < a).le
  have hh := norm_le_exp_proximity_on_closedBall ha.le haR
    (hqu.1.analyticOnNhd isOpen_ball |>.mono (closedBall_subset_ball hR1)) hza
  exact hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    ((quotient_proximity_le_pairGrowthMean (fun k => f k n) i j R).trans (hb n)) hQ))

end ModifiedCartan
