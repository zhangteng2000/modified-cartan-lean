import ModifiedCartan.SmallFourGrowth
import ModifiedCartan.CartanBoundedRatios

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- The bounded fourth-fraction branch contradicts the excluded initial
quotient reductions, once the preceding triple anchor step is available. -/
theorem small_four_fractions_excluded {p : ℕ} {f : Family p} {η a r₀ b A A₃ δ T : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (hηr : η < r₀) (har : a < r₀)
    (hrb : r₀ < b) (hb1 : b < 1) (hA : 0 ≤ A) (hA₃ : 0 ≤ A₃) (hδ : 0 < δ)
    (hT : 0 < T) (hTr : T ≤ r₀) (hf : UnitFamily f)
    (hno : NoVanishingQuotientSubsequence f (disk T))
    (hfinite : OnlyNegativeOneUnitLimits f (disk T))
    {i j k : Fin p} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hanchors : ∀ n i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧
      -A ≤ Real.log ‖f i n w/f j n w‖)
    (hWnonzero : ∀ n i j k, i ≠ j → i ≠ k → j ≠ k →
      ∃ w ∈ disk 1, wronskian ![f i n,f j n,f k n] w ≠ 0)
    (hWanchors : ∀ n, ∀ r ∈ Icc r₀ b, r+1/pairGrowthMean (fun i => f i n) r ≤ b →
      pairGrowthMean (fun i => f i n) (r+1/pairGrowthMean (fun i => f i n) r) ≤
        2*pairGrowthMean (fun i => f i n) r →
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∃ w : ℂ, ‖w‖ ≤ a ∧
        normalizedWronskian ![f i n,f j n,f k n] w ≠ 0 ∧
        -A₃*(Real.log (pairGrowthMean (fun i => f i n) r)+1) ≤
          Real.log ‖normalizedWronskian ![f i n,f j n,f k n] w‖)
    (hcircles : ∀ n, ∃ S : Set ℝ, S ⊆ Icc r₀ b ∧ ENNReal.ofReal δ ≤ volume S ∧
      ∀ r ∈ S, ∀ i j, i ≠ j → ∃ k l : Fin p, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
        ∀ z ∈ sphere (0 : ℂ) r,
        ‖wronskian ![f k n,f l n] z*wronskian ![f k n,f l n,f i n,f j n] z/
          (wronskian ![f k n,f l n,f i n] z*wronskian ![f k n,f l n,f j n] z)‖ ≤ 1) : False := by
  obtain ⟨C,hC,hbound⟩ := pairGrowth_bounded_of_small_four_fractions
    hη ha hηr har hrb hb1 hA hA₃ hδ p
  have hgrowth : ∀ n, pairGrowthMean (fun i => f i n) r₀ ≤ C := by
    intro n
    obtain ⟨S,hS,hsize,hfrac⟩ := hcircles n
    exact hbound (fun i => f i n) S (fun i => hf i n) (hanchors n)
      (hWnonzero n) (hWanchors n) hS hsize hfrac
  have hquot := locallyBounded_quotients_of_pairGrowth_at_radius
    (hη.trans hηr) (hrb.trans hb1) hf hgrowth
  have hTD : disk T ⊆ disk 1 := ball_subset_ball (hTr.trans (hrb.le.trans hb1.le))
  have hTrD : disk T ⊆ disk r₀ := ball_subset_ball hTr
  exact no_locallyBounded_three_chain ⟨0,by simpa [disk] using hT⟩ isOpen_ball
    (convex_ball (0 : ℂ) T).isPreconnected
    (fun i n => ⟨(hf i n).1.mono hTD,fun z hz => (hf i n).2 z (hTD hz)⟩)
    hno hfinite hij hjk hik (locallyBounded_mono (hquot i j) hTrD)
    (locallyBounded_mono (hquot j k) hTrD)

end ModifiedCartan
