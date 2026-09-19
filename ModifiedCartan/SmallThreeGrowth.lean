import ModifiedCartan.SmallThreeFractions
import ModifiedCartan.RadialZeros
import ModifiedCartan.GrowthBootstrap

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- A positive amount of bounded three-fraction circles gives a uniform
inner growth bound. All zero circles are removed without measure loss. -/
theorem pairGrowth_bounded_of_small_three_fractions {η a r₀ b A δ : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (hηr : η < r₀) (har : a < r₀)
    (hrb : r₀ < b) (hb1 : b < 1) (hA : 0 ≤ A) (hδ : 0 < δ) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Fin p → ℂ → ℂ) (S : Set ℝ),
      (∀ i, IsHolomorphicUnit (f i) (disk 1)) →
      (∀ i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧ -A ≤ Real.log ‖f i w/f j w‖) →
      (∀ i j, i ≠ j → ∃ w : ℂ, ‖w‖ ≤ a ∧ 1 ≤ ‖normalizedWronskian ![f i,f j] w‖) →
      S ⊆ Icc r₀ b → ENNReal.ofReal δ ≤ volume S →
      (∀ r ∈ S, ∀ i j, i ≠ j → ∃ k : Fin p, k ≠ i ∧ k ≠ j ∧ ∀ z ∈ sphere (0 : ℂ) r,
        ‖f k z*wronskian ![f k,f i,f j] z/(wronskian ![f k,f i] z*wronskian ![f k,f j] z)‖ ≤ 1) →
      pairGrowthMean f r₀ ≤ C := by
  classical
  obtain ⟨B,hB,hsmall⟩ := pairGrowth_bound_of_small_three_fractions hη ha hηr har (hrb.trans hb1) hA p
  obtain ⟨C,hC,hboot⟩ := growth_bound_from_large_radius_set hδ B
  refine ⟨C,hC,?_⟩
  intro f S hf hanchors hWanchors hS hsize hfractions
  let P := {ij : Fin p × Fin p // ij.1 ≠ ij.2}
  let W : P → ℂ → ℂ := fun ij => wronskian ![f ij.val.1,f ij.val.2]
  have hWh : ∀ ij, DifferentiableOn ℂ (W ij) (disk 1) := by
    intro ij
    apply (wronskian_analyticOnNhd _).differentiableOn
    intro j
    fin_cases j <;> simpa using (hf _).1.analyticOnNhd isOpen_ball
  have hWn : ∀ ij, ∃ w ∈ disk 1, W ij w ≠ 0 := by
    intro ij
    obtain ⟨w,hw,hn⟩ := hWanchors ij.val.1 ij.val.2 ij.property
    have hwD : w ∈ disk 1 := by simpa [disk] using hw.trans_lt (har.trans (hrb.trans hb1))
    refine ⟨w,hwD,?_⟩
    intro hzero
    have he : normalizedWronskian ![f ij.val.1,f ij.val.2] w = 0 := by
      rw [normalizedWronskian,show wronskian ![f ij.val.1,f ij.val.2] w = 0 from hzero,zero_div]
    norm_num [he] at hn
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
    hgrowth hanchors hWanchors
  · intro i j hij z hz
    exact hzero r hr ⟨(i,j),hij⟩ z hz
  · exact hfractions r (hS'S hr)

end ModifiedCartan
