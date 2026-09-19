import ModifiedCartan.CartanRadialCases
import ModifiedCartan.CartanSmallFour

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

theorem eventually_small_fourth_good_set {f : Family 4} {η a r₀ b A A₃ T : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (hηr : η < r₀) (har : a < r₀)
    (hrb : r₀ < b) (hb1 : b < 1) (hA : 0 ≤ A) (hA₃ : 0 ≤ A₃)
    (hT : 0 < T) (hTr : T ≤ r₀) (hf : UnitFamily f)
    (hno : NoVanishingQuotientSubsequence f (disk T))
    (hfinite : OnlyNegativeOneUnitLimits f (disk T))
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
 :
    ∀ᶠ n in atTop, volume (radialCommonGoodSet (fun σ : Equiv.Perm (Fin 4) =>
      fourthDerivedFraction (fun j => f (σ j) n)) r₀ b) ≤ ENNReal.ofReal ((b-r₀)/2) := by
  have he := eventually_not_of_no_strict_subsequence
    (P := fun n => ENNReal.ofReal ((b-r₀)/2) ≤ volume (radialCommonGoodSet
      (fun σ : Equiv.Perm (Fin 4) => fourthDerivedFraction (fun j => f (σ j) n)) r₀ b))
  apply (he ?_).mono (fun _ hn => (lt_of_not_ge hn).le)
  rintro ⟨φ,hφ,hsize⟩
  apply small_four_fractions_excluded hη ha hηr har hrb hb1 hA hA₃
    (by linarith : 0 < (b-r₀)/2) hT hTr (unitFamily_subsequence hf φ)
    (noVanishingQuotientSubsequence_subsequence hno hφ)
    (onlyNegativeOneUnitLimits_subsequence hfinite hφ)
    (i := (0 : Fin 4)) (j := 1) (k := 2) (by decide) (by decide) (by decide)
    (fun n => hanchors (φ n)) (fun n => hWnonzero (φ n)) (fun n => hWanchors (φ n))
  intro n
  refine ⟨radialCommonGoodSet (fun σ : Equiv.Perm (Fin 4) =>
    fourthDerivedFraction (fun j => f (σ j) (φ n))) r₀ b,fun _ hx => hx.1,hsize n,?_⟩
  intro r hr
  exact radialGood_fourth_pairs hr

end ModifiedCartan
