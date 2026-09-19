import ModifiedCartan.SmallThreeGrowth
import ModifiedCartan.CartanBoundedRatios

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- The bounded three-fraction branch is incompatible with exclusion of
Cartan's two earlier quotient-limit reductions. Radius sets may vary with
n and need not be measurable. No zero-free-circle premise remains. -/
theorem small_three_fractions_excluded {p : ℕ} {f : Family p} {η a r₀ b A δ T : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (hηr : η < r₀) (har : a < r₀)
    (hrb : r₀ < b) (hb1 : b < 1) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hT : 0 < T) (hTr : T ≤ r₀) (hf : UnitFamily f)
    (hno : NoVanishingQuotientSubsequence f (disk T))
    (hfinite : OnlyNegativeOneUnitLimits f (disk T))
    {i j k : Fin p} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hanchors : ∀ n i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧
      -A ≤ Real.log ‖f i n w/f j n w‖)
    (hWanchors : ∀ n i j, i ≠ j → ∃ w : ℂ, ‖w‖ ≤ a ∧
      1 ≤ ‖normalizedWronskian ![f i n,f j n] w‖)
    (hcircles : ∀ n, ∃ S : Set ℝ, S ⊆ Icc r₀ b ∧ ENNReal.ofReal δ ≤ volume S ∧
      ∀ r ∈ S, ∀ i j, i ≠ j → ∃ k : Fin p, k ≠ i ∧ k ≠ j ∧ ∀ z ∈ sphere (0 : ℂ) r,
        ‖f k n z*wronskian ![f k n,f i n,f j n] z/
          (wronskian ![f k n,f i n] z*wronskian ![f k n,f j n] z)‖ ≤ 1) : False := by
  obtain ⟨C,hC,hbound⟩ := pairGrowth_bounded_of_small_three_fractions
    hη ha hηr har hrb hb1 hA hδ p
  have hgrowth : ∀ n, pairGrowthMean (fun i => f i n) r₀ ≤ C := by
    intro n
    obtain ⟨S,hS,hsize,hfrac⟩ := hcircles n
    exact hbound (fun i => f i n) S (fun i => hf i n) (hanchors n) (hWanchors n) hS hsize hfrac
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
