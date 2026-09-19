import ModifiedCartan.DerivedFractionRadii

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

theorem large_value_point_of_small_good_set {ι : Type*} [Fintype ι] (F : ι → ℂ → ℂ) {b c : ℝ}
    (hbc : b < c)
    (hgood : volume (radialCommonGoodSet F b c) ≤ ENNReal.ofReal ((c-b)/2)) :
    ∃ i : ι, ∃ z : ℂ, b ≤ ‖z‖ ∧ ‖z‖ ≤ c ∧ 1 < ‖F i z‖ := by
  obtain ⟨i,hi⟩ := exists_large_orientation F hbc hgood
  have hne : (radialLargeValueSet (F i) b c).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn,measure_empty] at hi
    exact (not_lt_of_ge (by positivity)) hi
  obtain ⟨r,hr,z,hz,hlarge⟩ := hne
  exact ⟨i,z,hz ▸ hr.1,hz ▸ hr.2,hlarge⟩

theorem normalizedWronskian_three_nonzero_of_small_good_set {g : Fin 3 → ℂ → ℂ} {b c : ℝ}
    (hbc : b < c) (hc1 : c < 1) (hg : ∀ j, IsHolomorphicUnit (g j) (disk 1))
    (hgood : volume (radialCommonGoodSet (fun σ : Equiv.Perm (Fin 3) =>
      thirdDerivedFraction (g ∘ σ)) b c) ≤ ENNReal.ofReal ((c-b)/2)) :
    ∃ w : ℂ, ‖w‖ ≤ c ∧ normalizedWronskian g w ≠ 0 := by
  obtain ⟨σ,z,_,hzc,hlarge⟩ := large_value_point_of_small_good_set _ hbc hgood
  have hzD : z ∈ disk 1 := by simpa [disk] using hzc.trans_lt hc1
  have hW : wronskian (g ∘ σ) z ≠ 0 := by
    intro hz
    norm_num [thirdDerivedFraction,hz] at hlarge
  have hN : normalizedWronskian (g ∘ σ) z ≠ 0 := div_ne_zero hW
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hg (σ i)).2 z hzD))
  refine ⟨z,hzc,?_⟩
  apply norm_ne_zero_iff.mp
  rw [← normalizedWronskian_norm_comp_perm g σ z]
  exact norm_ne_zero_iff.mpr hN

theorem normalizedWronskian_four_nonzero_of_small_good_set {g : Fin 4 → ℂ → ℂ} {b c : ℝ}
    (hbc : b < c) (hc1 : c < 1) (hg : ∀ j, IsHolomorphicUnit (g j) (disk 1))
    (hgood : volume (radialCommonGoodSet (fun σ : Equiv.Perm (Fin 4) =>
      fourthDerivedFraction (g ∘ σ)) b c) ≤ ENNReal.ofReal ((c-b)/2)) :
    ∃ w : ℂ, ‖w‖ ≤ c ∧ normalizedWronskian g w ≠ 0 := by
  obtain ⟨σ,z,_,hzc,hlarge⟩ := large_value_point_of_small_good_set _ hbc hgood
  have hzD : z ∈ disk 1 := by simpa [disk] using hzc.trans_lt hc1
  have hW : wronskian (g ∘ σ) z ≠ 0 := by
    intro hz
    norm_num [fourthDerivedFraction,hz] at hlarge
  have hN : normalizedWronskian (g ∘ σ) z ≠ 0 := div_ne_zero hW
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hg (σ i)).2 z hzD))
  refine ⟨z,hzc,?_⟩
  apply norm_ne_zero_iff.mp
  rw [← normalizedWronskian_norm_comp_perm g σ z]
  exact norm_ne_zero_iff.mpr hN

end ModifiedCartan
