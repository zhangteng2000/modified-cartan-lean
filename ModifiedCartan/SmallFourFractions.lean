import ModifiedCartan.PairProximityAlternatives
import ModifiedCartan.NormalizedWronskianGrowth
import ModifiedCartan.QuotientAnchors
import ModifiedCartan.WronskianFourProximity

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- The bounded four-term derived-fraction branch. The lower-order triple
anchors may have logarithmic loss, as supplied by the preceding anchor step. -/
theorem pairGrowth_bound_of_small_four_fractions {η a r₀ A A₃ : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (hηr : η < r₀) (har : a < r₀)
    (hr1 : r₀ < 1) (hA : 0 ≤ A) (hA₃ : 0 ≤ A₃) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fin p → ℂ → ℂ) (r s M : ℝ),
      (∀ i, IsHolomorphicUnit (f i) (disk 1)) →
      r₀ ≤ r → r < s → s < 1 → 1 ≤ M → s-r = 1/M → pairGrowthMean f s ≤ 2*M →
      (∀ i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧ -A ≤ Real.log ‖f i w/f j w‖) →
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∃ w : ℂ, ‖w‖ ≤ a ∧
        normalizedWronskian ![f i,f j,f k] w ≠ 0 ∧
        -A₃*(Real.log M+1) ≤ Real.log ‖normalizedWronskian ![f i,f j,f k] w‖) →
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ z ∈ sphere (0 : ℂ) r,
        wronskian ![f i,f j,f k] z ≠ 0) →
      (∀ i j, i ≠ j → ∃ k l : Fin p, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
        ∀ z ∈ sphere (0 : ℂ) r,
        ‖wronskian ![f k,f l] z*wronskian ![f k,f l,f i,f j] z/
          (wronskian ![f k,f l,f i] z*wronskian ![f k,f l,f j] z)‖ ≤ 1) →
      pairGrowthMean f r ≤ C*(Real.log M+1) := by
  obtain ⟨B,hB,hbound⟩ := normalizedWronskian_growth_bound hη hηr (Real.exp_pos (-A)) 3
  obtain ⟨V,hV,hinv⟩ := proximityMean_inv_growth_bound ha har hA₃ hB
  let T := 2*Real.pi+B+V
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨C,hC,hclose⟩ := pairGrowth_bound_of_proximity_alternatives hη.le hηr hA hT p
  refine ⟨C,hC,?_⟩
  intro f r s M hf hr hrs hs hM hgap hMs hanchors hWanchors hWcircle hfractions
  let ℓ := Real.log M+1
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith [Real.log_nonneg hM]
  have hr0 : 0 < r := hη.trans (hηr.trans_le hr)
  have hr' : r < 1 := hrs.trans hs
  have hunit (i j k : Fin p) : ∀ l : Fin 3, IsHolomorphicUnit (![f i,f j,f k] l) (disk 1) := by
    intro l
    fin_cases l <;> simpa using hf _
  have htriple (i j k : Fin p) : proximityMean (normalizedWronskian ![f i,f j,f k]) r ≤ B*ℓ := by
    apply hbound ![f i,f j,f k] (f i) r s M (hunit i j k) (hf i)
    · intro l
      fin_cases l <;> simpa using diskSupNorm_ge_exp_of_log_anchor (hηr.trans hr1)
        (unit_quotient (hf _) (hf i)) (hanchors _ i)
    · exact hr
    · exact hrs
    · exact hs
    · exact hM
    · exact hgap
    · intro l
      fin_cases l <;> simpa using (quotient_proximity_le_pairGrowthMean f _ i s).trans hMs
  have htripleInv (i j k : Fin p) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      proximityMean (fun z => (normalizedWronskian ![f i,f j,f k] z)⁻¹) r ≤ V*ℓ := by
    exact hinv (normalizedWronskian ![f i,f j,f k]) r M hr hr'.le hM
      ((normalizedWronskian_analyticOnNhd
        (fun l => (hunit i j k l).1.analyticOnNhd isOpen_ball) (fun l => (hunit i j k l).2)).mono
        (closedBall_subset_ball hr')) (htriple i j k) (hWanchors i j k hij hik hjk)
  apply hclose f r M hf hr hr' hM hanchors
  intro i j hij
  obtain ⟨k,l,hkl,hki,hkj,hli,hlj,hd⟩ := hfractions i j hij
  have hc := wronskian_four_circle_proximity_alternative hr0 hr' (by norm_num : (0 : ℝ) ≤ 1)
    (g := ![f k,f l,f i,f j]) (by intro t; fin_cases t <;> simpa using hf _)
    (by simpa using hWcircle k l i hkl hki hli) (by simpa using hWcircle k l j hkl hkj hlj)
    (by simpa using hd)
  have hπ : 2*Real.pi*r ≤ 2*Real.pi*ℓ :=
    mul_le_mul_of_nonneg_left (hr'.le.trans hℓ) (by positivity)
  rcases hc with hc | hc
  · left
    have h1 := htriple k l j
    have h2 := htripleInv k l i hkl hki hli
    change proximityMean (fun z => f i z/f j z) r ≤ 2*Real.pi*r*1+
      proximityMean (normalizedWronskian ![f k,f l,f j]) r+
      proximityMean (fun z => (normalizedWronskian ![f k,f l,f i] z)⁻¹) r at hc
    dsimp [T]
    nlinarith
  · right
    have h1 := htriple k l i
    have h2 := htripleInv k l j hkl hkj hlj
    change proximityMean (fun z => f j z/f i z) r ≤ 2*Real.pi*r*1+
      proximityMean (normalizedWronskian ![f k,f l,f i]) r+
      proximityMean (fun z => (normalizedWronskian ![f k,f l,f j] z)⁻¹) r at hc
    dsimp [T]
    nlinarith

end ModifiedCartan
