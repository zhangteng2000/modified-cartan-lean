import ModifiedCartan.CartanRadialCases
import ModifiedCartan.CartanPairSelection
import ModifiedCartan.OrientedWronskianGrowth
import ModifiedCartan.RadialWronskianNonzero
import ModifiedCartan.CartanInverseEndgame

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- The higher-Wronskian endgame for four units is impossible after the
initial quotient reductions have been excluded. The triple good-radius
condition is constructed by the already proved case exclusion. -/
theorem four_anchored_subfamily_impossible {f : Family 4} {η A L : ℝ}
    (hL : 0 < L) (hL1 : L < 1) (hη : 0 < η) (hηL : η < L) (hA : 0 ≤ A)
    (hf : UnitFamily f) (hs : ZeroSum f)
    (hno : NoVanishingQuotientSubsequence f (disk L))
    (hfinite : OnlyNegativeOneUnitLimits f (disk L))
    (hanchors : ∀ n i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧
      -A ≤ Real.log ‖f i n w/f j n w‖)
    (hWanchors : ∀ (n : ℕ) (i j : Fin 3), i ≠ j → ∃ w : ℂ, ‖w‖ ≤ L ∧
      1 ≤ ‖normalizedWronskian ![f i.castSucc n,f j.castSucc n] w‖) : False := by
  let b := L+(1-L)/6
  let c := L+2*(1-L)/6
  let T := L+3*(1-L)/6
  let R := L+4*(1-L)/6
  let r₀ := L+5*(1-L)/6
  have hLb : L < b := by dsimp [b]; linarith
  have hbc : b < c := by dsimp [b,c]; linarith
  have hcT : c < T := by dsimp [c,T]; linarith
  have hTR : T < R := by dsimp [T,R]; linarith
  have hRr : R < r₀ := by dsimp [R,r₀]; linarith
  have hr1 : r₀ < 1 := by dsimp [r₀]; linarith
  have hLr : L < r₀ := hLb.trans (hbc.trans (hcT.trans (hTR.trans hRr)))
  let g : Family 3 := fun i => f i.castSucc
  have hgood := eventually_small_third_good_set hη hL.le (hηL.trans hLb) hLb
    hbc (hcT.trans (hTR.trans (hRr.trans hr1))) hA hL hLb.le
    (fun i n => hf i.castSucc n)
    (noVanishingQuotientSubsequence_reindex hno Fin.castSucc)
    (onlyNegativeOneUnitLimits_reindex hfinite (Fin.castSucc_injective 3))
    (fun n i j => hanchors n i.castSucc j.castSucc) hWanchors
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  obtain ⟨D,C,hD,hC,hbound⟩ := wronskian_three_growth_of_small_good_set hL (hL.trans hLb).le hbc
    (hLb.trans (hbc.trans hcT)) hcT hTR hRr hr1 hη (hηL.trans hLr) (Real.exp_pos (-A))
  obtain ⟨B,_,hclose⟩ := pairGrowth_bounded_of_inverseWronskian_control
    hη (hηL.trans hLr) hr1 hA hC 3
  let F : Family 4 := subsequence f (fun n => N+n)
  have hFu : UnitFamily F := unitFamily_subsequence hf _
  have hFs : ZeroSum F := zeroSum_subsequence hs _
  have hG (n : ℕ) := hN (N+n) (by omega)
  have hnonzero (n : ℕ) : ∃ w ∈ disk 1,
      normalizedWronskian (fun j : Fin 3 => F j.castSucc n) w ≠ 0 := by
    obtain ⟨w,hw,hn⟩ := normalizedWronskian_three_nonzero_of_small_good_set hbc
      (hcT.trans (hTR.trans (hRr.trans hr1))) (fun j => hFu j.castSucc n) (hG n)
    exact ⟨w,by simpa [disk] using hw.trans_lt (hcT.trans (hTR.trans (hRr.trans hr1))),hn⟩
  have hinv (n : ℕ) : ∀ r ∈ Icc r₀ ((r₀+1)/2),
      r+1/pairGrowthMean (fun i => F i n) r ≤ (r₀+1)/2 →
      pairGrowthMean (fun i => F i n) (r+1/pairGrowthMean (fun i => F i n) r) ≤
        2*pairGrowthMean (fun i => F i n) r →
      proximityMean (fun z => (normalizedWronskian (fun j : Fin 3 => F j.castSucc n) z)⁻¹) r ≤
        C*(Real.log (pairGrowthMean (fun i => F i n) r)+1) := by
    intro r hr hstep hgrow
    let M := pairGrowthMean (fun i => F i n) r
    have hM : 1 ≤ M := pairGrowthMean_ge_one _ _
    have hM0 : 0 < M := by linarith
    have hs1 : r+1/M < 1 := lt_of_le_of_lt hstep (by linarith)
    apply (hbound (fun j : Fin 3 => F j.castSucc n) r (r+1/M) M
      (fun j => hFu j.castSucc n) hr.1 (lt_add_of_pos_right r (one_div_pos.mpr hM0))
      hs1 hM (by ring) ?_ ?_ (hWanchors (N+n)) (hG n)).2
    · intro i j
      exact diskSupNorm_ge_exp_of_log_anchor (hηL.trans hL1)
        (unit_quotient (hFu i.castSucc n) (hFu j.castSucc n))
        (hanchors (N+n) i.castSucc j.castSucc)
    · intro i j
      exact (quotient_proximity_le_pairGrowthMean (fun k => F k n) i.castSucc j.castSucc _).trans hgrow
  have hgrowth : ∀ n, pairGrowthMean (fun i => F i n) r₀ ≤ B := fun n =>
    hclose (fun i => F i n) (fun i => hFu i n) (hFs n) (hanchors (N+n)) (hnonzero n) (hinv n)
  have hquot := locallyBounded_quotients_of_pairGrowth_at_radius (hL.trans hLr) hr1 hFu hgrowth
  have hshift : StrictMono (fun n : ℕ => N+n) := fun i j hij => Nat.add_lt_add_left hij N
  have hsub : disk L ⊆ disk 1 := ball_subset_ball hL1.le
  exact no_locallyBounded_three_chain ⟨0,by simpa [disk] using hL⟩ isOpen_ball
    (convex_ball (0 : ℂ) L).isPreconnected
    (fun i n => ⟨(hFu i n).1.mono hsub,fun z hz => (hFu i n).2 z (hsub hz)⟩)
    (noVanishingQuotientSubsequence_subsequence hno hshift)
    (onlyNegativeOneUnitLimits_subsequence hfinite hshift)
    (a := (0 : Fin 4)) (b := 1) (c := 2) (by decide) (by decide) (by decide)
    (locallyBounded_mono (hquot 0 1) (ball_subset_ball hLr.le))
    (locallyBounded_mono (hquot 1 2) (ball_subset_ball hLr.le))

end ModifiedCartan
