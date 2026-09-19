import ModifiedCartan.DerivedFractionRadii
import ModifiedCartan.FiniteCaseExclusion
import ModifiedCartan.CartanSmallThree

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

theorem eventually_small_third_good_set {f : Family 3} {η a b c A T : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (hηb : η < b) (hab : a < b)
    (hbc : b < c) (hc1 : c < 1) (hA : 0 ≤ A)
    (hT : 0 < T) (hTb : T ≤ b) (hf : UnitFamily f)
    (hno : NoVanishingQuotientSubsequence f (disk T))
    (hfinite : OnlyNegativeOneUnitLimits f (disk T))
    (hanchors : ∀ n i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧
      -A ≤ Real.log ‖f i n w/f j n w‖)
    (hWanchors : ∀ n i j, i ≠ j → ∃ w : ℂ, ‖w‖ ≤ a ∧
      1 ≤ ‖normalizedWronskian ![f i n,f j n] w‖) :
    ∀ᶠ n in atTop,
      volume (radialCommonGoodSet (fun σ : Equiv.Perm (Fin 3) =>
        thirdDerivedFraction (fun j => f (σ j) n)) b c) ≤ ENNReal.ofReal ((c-b)/2) := by
  have he := eventually_not_of_no_strict_subsequence
    (P := fun n => ENNReal.ofReal ((c-b)/2) ≤ volume (radialCommonGoodSet
      (fun σ : Equiv.Perm (Fin 3) => thirdDerivedFraction (fun j => f (σ j) n)) b c))
  apply (he ?_).mono (fun _ hn => (lt_of_not_ge hn).le)
  rintro ⟨φ,hφ,hsize⟩
  apply small_three_fractions_excluded hη ha hηb hab hbc hc1 hA (by linarith : 0 < (c-b)/2)
    hT hTb (unitFamily_subsequence hf φ)
    (noVanishingQuotientSubsequence_subsequence hno hφ)
    (onlyNegativeOneUnitLimits_subsequence hfinite hφ)
    (i := (0 : Fin 3)) (j := 1) (k := 2) (by decide) (by decide) (by decide)
    (fun n => hanchors (φ n)) (fun n => hWanchors (φ n))
  intro n
  refine ⟨radialCommonGoodSet (fun σ : Equiv.Perm (Fin 3) =>
    thirdDerivedFraction (fun j => f (σ j) (φ n))) b c,fun _ hx => hx.1,hsize n,?_⟩
  intro r hr
  exact radialGood_third_pairs hr

end ModifiedCartan
