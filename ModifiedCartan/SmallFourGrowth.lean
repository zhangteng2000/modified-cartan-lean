import ModifiedCartan.SmallFourFractions
import ModifiedCartan.RadialZeros
import ModifiedCartan.GrowthBootstrap

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- Uniform inner growth for the bounded fourth-fraction case, allowing the
triple anchors to depend on the selected growth-controlled radius. -/
theorem pairGrowth_bounded_of_small_four_fractions {η a r₀ b A A₃ δ : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (hηr : η < r₀) (har : a < r₀)
    (hrb : r₀ < b) (hb1 : b < 1) (hA : 0 ≤ A) (hA₃ : 0 ≤ A₃) (hδ : 0 < δ) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Fin p → ℂ → ℂ) (S : Set ℝ),
      (∀ i, IsHolomorphicUnit (f i) (disk 1)) →
      (∀ i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧ -A ≤ Real.log ‖f i w/f j w‖) →
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∃ w ∈ disk 1, wronskian ![f i,f j,f k] w ≠ 0) →
      (∀ r ∈ Icc r₀ b, r+1/pairGrowthMean f r ≤ b →
        pairGrowthMean f (r+1/pairGrowthMean f r) ≤ 2*pairGrowthMean f r →
        ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∃ w : ℂ, ‖w‖ ≤ a ∧
          normalizedWronskian ![f i,f j,f k] w ≠ 0 ∧
          -A₃*(Real.log (pairGrowthMean f r)+1) ≤ Real.log ‖normalizedWronskian ![f i,f j,f k] w‖) →
      S ⊆ Icc r₀ b → ENNReal.ofReal δ ≤ volume S →
      (∀ r ∈ S, ∀ i j, i ≠ j → ∃ k l : Fin p, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
        ∀ z ∈ sphere (0 : ℂ) r,
        ‖wronskian ![f k,f l] z*wronskian ![f k,f l,f i,f j] z/
          (wronskian ![f k,f l,f i] z*wronskian ![f k,f l,f j] z)‖ ≤ 1) →
      pairGrowthMean f r₀ ≤ C := by
  classical
  obtain ⟨B,hB,hsmall⟩ := pairGrowth_bound_of_small_four_fractions hη ha hηr har (hrb.trans hb1) hA hA₃ p
  obtain ⟨C,hC,hboot⟩ := growth_bound_from_large_radius_set hδ B
  refine ⟨C,hC,?_⟩
  intro f S hf hanchors hWnonzero hWanchors hS hsize hfractions
  let P := {ijk : Fin p × Fin p × Fin p //
    ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2}
  let W : P → ℂ → ℂ := fun ijk => wronskian ![f ijk.val.1,f ijk.val.2.1,f ijk.val.2.2]
  have hWh : ∀ ijk, DifferentiableOn ℂ (W ijk) (disk 1) := by
    intro ijk
    apply (wronskian_analyticOnNhd _).differentiableOn
    intro j
    fin_cases j <;> simpa using (hf _).1.analyticOnNhd isOpen_ball
  have hWn : ∀ ijk, ∃ w ∈ disk 1, W ijk w ≠ 0 := fun ijk =>
    hWnonzero ijk.val.1 ijk.val.2.1 ijk.val.2.2 ijk.property.1 ijk.property.2.1 ijk.property.2.2
  obtain ⟨S',hS'S,hvol,hzero⟩ := exists_zero_free_circle_subset W
    (hη.le.trans (hηr.le.trans hrb.le)) hb1 hWh hWn S hS
  have hsub : Icc r₀ b ⊆ Ico 0 1 := fun r hr =>
    ⟨hη.le.trans (hηr.le.trans hr.1),hr.2.trans_lt hb1⟩
  apply hboot (pairGrowthMean f) r₀ b S' hrb.le
    ((pairGrowthMean_continuousOn hf).mono hsub) ((pairGrowthMean_monotoneOn hf).mono hsub)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (pairGrowthMean_ge_one f r₀)) (hS'S.trans hS)
    (by rwa [hvol])
  intro r hr hstep hgrowth
  have hMr : 1 ≤ pairGrowthMean f r := pairGrowthMean_ge_one f r
  have hMr0 : 0 < pairGrowthMean f r := by linarith
  apply hsmall f r (r+1/pairGrowthMean f r) (pairGrowthMean f r) hf (hS (hS'S hr)).1
    (lt_add_of_pos_right r (one_div_pos.mpr hMr0)) (hstep.trans_lt hb1) hMr (by ring)
    hgrowth hanchors (hWanchors r (hS (hS'S hr)) hstep hgrowth)
  · intro i j k hij hik hjk z hz
    exact hzero r hr ⟨(i,j,k),hij,hik,hjk⟩ z hz
  · exact hfractions r (hS'S hr)

end ModifiedCartan
