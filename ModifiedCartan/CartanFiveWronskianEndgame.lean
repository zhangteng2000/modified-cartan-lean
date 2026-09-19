import ModifiedCartan.TripleAnchorsFromCases
import ModifiedCartan.CartanFourthRadialCase
import ModifiedCartan.CartanInverseEndgame

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- The complete higher-Wronskian endgame for five functions. Both radial
case exclusions and every intermediate triple anchor are constructed. -/
theorem five_anchored_subfamily_impossible {f : Family 5} {η A L : ℝ}
    (hL : 0 < L) (hL1 : L < 1) (hη : 0 < η) (hηL : η < L) (hA : 0 ≤ A)
    (hf : UnitFamily f) (hs : ZeroSum f)
    (hno : NoVanishingQuotientSubsequence f (disk L))
    (hfinite : OnlyNegativeOneUnitLimits f (disk L))
    (hanchors : ∀ n i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧
      -A ≤ Real.log ‖f i n w/f j n w‖)
    (hWanchors : ∀ (n : ℕ) (i j : Fin 4), i ≠ j → ∃ w : ℂ, ‖w‖ ≤ L ∧
      1 ≤ ‖normalizedWronskian ![f i.castSucc n,f j.castSucc n] w‖) : False := by
  let q : ℕ → ℝ := fun i => L+(i : ℝ)*((1-L)/12)
  have hq0 : q 0 = L := by simp [q]
  have hq : StrictMono q := by
    intro i j hij
    change L+(i : ℝ)*((1-L)/12) < L+(j : ℝ)*((1-L)/12)
    have hc : (i : ℝ) < j := by exact_mod_cast hij
    have hh := mul_lt_mul_of_pos_right hc (by linarith : 0 < (1-L)/12)
    linarith
  have hLq (i : ℕ) : L ≤ q i := by simpa only [hq0] using hq.monotone (Nat.zero_le i)
  have hqpos (i : ℕ) : 0 < q i := hL.trans_le (hLq i)
  have hηq (i : ℕ) : η < q i := hηL.trans_le (hLq i)
  have hq1 (i : ℕ) (hi : i < 12) : q i < 1 := by
    have hc : (i : ℝ) < 12 := by exact_mod_cast hi
    have hp : 0 < (1-L)/12 := by linarith
    have hh := mul_lt_mul_of_pos_right hc hp
    dsimp [q]
    linarith
  have hLq1 : L < q 1 := by simpa only [hq0] using hq (by omega : 0 < 1)
  let g : Family 4 := fun i => f i.castSucc
  have hgu : UnitFamily g := fun i n => hf i.castSucc n
  have hgn : NoVanishingQuotientSubsequence g (disk L) :=
    noVanishingQuotientSubsequence_reindex hno Fin.castSucc
  have hgf : OnlyNegativeOneUnitLimits g (disk L) :=
    onlyNegativeOneUnitLimits_reindex hfinite (Fin.castSucc_injective 4)
  obtain ⟨D₃,C₃,hD₃,_,htriples⟩ := eventually_uniform_triple_anchors hL hLq1
    (hq (by omega : 1 < 2)) (hq (by omega : 2 < 3)) (hq (by omega : 3 < 4))
    (hq (by omega : 4 < 5)) (hq1 5 (by omega)) hη hηL hA hgu hgn hgf
    (fun n i j => hanchors n i.castSucc j.castSucc) hWanchors
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp htriples
  let g₁ : Family 4 := subsequence g (fun n => N₁+n)
  have hshift₁ : StrictMono (fun n : ℕ => N₁+n) := fun i j hij => Nat.add_lt_add_left hij N₁
  have htrip (n : ℕ) := hN₁ (N₁+n) (by omega)
  have hWnz (n : ℕ) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ∃ w ∈ disk 1, wronskian ![g₁ i n,g₁ j n,g₁ k n] w ≠ 0 := by
    let v := tripleIndexEmbedding i j k hij hik hjk
    have he : (fun t : Fin 3 => g (v t) (N₁+n)) = ![g₁ i n,g₁ j n,g₁ k n] := by
      funext t
      fin_cases t <;> rfl
    obtain ⟨w,hw,hn⟩ := (htrip n v).1
    rw [he] at hn
    refine ⟨w,by simpa [disk] using hw.trans_lt (hq1 2 (by omega)),?_⟩
    intro hz
    exact hn (by simp only [normalizedWronskian,hz,zero_div])
  have hWa (n : ℕ) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (r s M : ℝ) (hr : q 5 ≤ r) (hrs : r < s) (hs1 : s < 1) (hM : 1 ≤ M) (hgap : s-r = 1/M)
      (hmeans : ∀ i j, proximityMean (fun z => g₁ i n z/g₁ j n z) s ≤ 2*M) :
      ∃ w : ℂ, ‖w‖ ≤ q 2 ∧ normalizedWronskian ![g₁ i n,g₁ j n,g₁ k n] w ≠ 0 ∧
        -D₃*(Real.log M+1) ≤ Real.log ‖normalizedWronskian ![g₁ i n,g₁ j n,g₁ k n] w‖ := by
    let v := tripleIndexEmbedding i j k hij hik hjk
    have he : (fun t : Fin 3 => g (v t) (N₁+n)) = ![g₁ i n,g₁ j n,g₁ k n] := by
      funext t
      fin_cases t <;> rfl
    have hh := ((htrip n v).2 r s M hr hrs hs1 hM hgap hmeans).1
    simpa only [he] using hh
  have hWcontrol : ∀ n, ∀ r ∈ Icc (q 6) (q 7), r+1/pairGrowthMean (fun i => g₁ i n) r ≤ q 7 →
      pairGrowthMean (fun i => g₁ i n) (r+1/pairGrowthMean (fun i => g₁ i n) r) ≤
        2*pairGrowthMean (fun i => g₁ i n) r →
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∃ w : ℂ, ‖w‖ ≤ q 2 ∧
        normalizedWronskian ![g₁ i n,g₁ j n,g₁ k n] w ≠ 0 ∧
        -D₃*(Real.log (pairGrowthMean (fun i => g₁ i n) r)+1) ≤
          Real.log ‖normalizedWronskian ![g₁ i n,g₁ j n,g₁ k n] w‖ := by
    intro n r hr hstep hgrow i j k hij hik hjk
    let M := pairGrowthMean (fun i => g₁ i n) r
    have hM : 1 ≤ M := pairGrowthMean_ge_one _ _
    have hM0 : 0 < M := by linarith
    exact hWa n i j k hij hik hjk r (r+1/M) M
      ((hq (by omega : 5 < 6)).le.trans hr.1) (lt_add_of_pos_right r (one_div_pos.mpr hM0))
      (hstep.trans_lt (hq1 7 (by omega))) hM (by ring)
      (fun i j => (quotient_proximity_le_pairGrowthMean (fun i => g₁ i n) i j _).trans hgrow)
  have hgood₄ := eventually_small_fourth_good_set hη (hqpos 2).le (hηq 6)
    (hq (by omega : 2 < 6)) (hq (by omega : 6 < 7)) (hq1 7 (by omega)) hA hD₃ hL (hLq 6)
    (unitFamily_subsequence hgu _) (noVanishingQuotientSubsequence_subsequence hgn hshift₁)
    (onlyNegativeOneUnitLimits_subsequence hgf hshift₁)
    (fun n i j => hanchors (N₁+n) i.castSucc j.castSucc) hWnz hWcontrol
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp hgood₄
  let F : Family 5 := subsequence f (fun n => N₁+(N₂+n))
  have hFu : UnitFamily F := unitFamily_subsequence hf _
  have hFs : ZeroSum F := zeroSum_subsequence hs _
  have hG (n : ℕ) := hN₂ (N₂+n) (by omega)
  obtain ⟨D₄,C₄,_,hC₄,hbound⟩ := wronskian_four_growth_of_small_good_set
    (hqpos 2) (hqpos 6).le (hq (by omega : 6 < 7)) (hq (by omega : 2 < 8))
    (hq (by omega : 7 < 8)) (hq (by omega : 8 < 9)) (hq (by omega : 9 < 10))
    (hq1 10 (by omega)) hη (hηq 10) (Real.exp_pos (-A)) hD₃
  obtain ⟨B,_,hclose⟩ := pairGrowth_bounded_of_inverseWronskian_control
    hη (hηq 10) (hq1 10 (by omega)) hA hC₄ 4
  have hnonzero (n : ℕ) : ∃ w ∈ disk 1,
      normalizedWronskian (fun j : Fin 4 => F j.castSucc n) w ≠ 0 := by
    obtain ⟨w,hw,hn⟩ := normalizedWronskian_four_nonzero_of_small_good_set
      (hq (by omega : 6 < 7)) (hq1 7 (by omega)) (fun j => hFu j.castSucc n) (hG n)
    exact ⟨w,by simpa [disk] using hw.trans_lt (hq1 7 (by omega)),hn⟩
  have hinv (n : ℕ) : ∀ r ∈ Icc (q 10) ((q 10+1)/2),
      r+1/pairGrowthMean (fun i => F i n) r ≤ (q 10+1)/2 →
      pairGrowthMean (fun i => F i n) (r+1/pairGrowthMean (fun i => F i n) r) ≤
        2*pairGrowthMean (fun i => F i n) r →
      proximityMean (fun z => (normalizedWronskian (fun j : Fin 4 => F j.castSucc n) z)⁻¹) r ≤
        C₄*(Real.log (pairGrowthMean (fun i => F i n) r)+1) := by
    intro r hr hstep hgrow
    let M := pairGrowthMean (fun i => F i n) r
    have hM : 1 ≤ M := pairGrowthMean_ge_one _ _
    have hM0 : 0 < M := by linarith
    have hrs : r < r+1/M := lt_add_of_pos_right r (one_div_pos.mpr hM0)
    have hs1 : r+1/M < 1 := hstep.trans_lt (by have := hq1 10 (by omega); linarith)
    have hmean (i j : Fin 4) : proximityMean (fun z => F i.castSucc n z/F j.castSucc n z) (r+1/M) ≤ 2*M :=
      (quotient_proximity_le_pairGrowthMean (fun k => F k n) i.castSucc j.castSucc _).trans hgrow
    apply (hbound (fun j : Fin 4 => F j.castSucc n) r (r+1/M) M (fun j => hFu j.castSucc n)
      hr.1 hrs hs1 hM (by ring) ?_ hmean ?_ (hG n)).2
    · intro i j
      exact diskSupNorm_ge_exp_of_log_anchor (hηL.trans hL1)
        (unit_quotient (hFu i.castSucc n) (hFu j.castSucc n))
        (hanchors (N₁+(N₂+n)) i.castSucc j.castSucc)
    · intro i j k hij hik hjk
      exact hWa (N₂+n) i j k hij hik hjk r (r+1/M) M
        ((hq (by omega : 5 < 10)).le.trans hr.1) hrs hs1 hM (by ring) hmean
  have hgrowth : ∀ n, pairGrowthMean (fun i => F i n) (q 10) ≤ B := fun n =>
    hclose (fun i => F i n) (fun i => hFu i n) (hFs n) (hanchors (N₁+(N₂+n))) (hnonzero n) (hinv n)
  have hquot := locallyBounded_quotients_of_pairGrowth_at_radius (hqpos 10) (hq1 10 (by omega)) hFu hgrowth
  have hshift : StrictMono (fun n : ℕ => N₁+(N₂+n)) := fun i j hij =>
    Nat.add_lt_add_left (Nat.add_lt_add_left hij N₂) N₁
  have hsub : disk L ⊆ disk 1 := ball_subset_ball hL1.le
  exact no_locallyBounded_three_chain ⟨0,by simpa [disk] using hL⟩ isOpen_ball
    (convex_ball (0 : ℂ) L).isPreconnected
    (fun i n => ⟨(hFu i n).1.mono hsub,fun z hz => (hFu i n).2 z (hsub hz)⟩)
    (noVanishingQuotientSubsequence_subsequence hno hshift)
    (onlyNegativeOneUnitLimits_subsequence hfinite hshift)
    (a := (0 : Fin 5)) (b := 1) (c := 2) (by decide) (by decide) (by decide)
    (locallyBounded_mono (hquot 0 1) (ball_subset_ball (hLq 10)))
    (locallyBounded_mono (hquot 1 2) (ball_subset_ball (hLq 10)))

end ModifiedCartan
