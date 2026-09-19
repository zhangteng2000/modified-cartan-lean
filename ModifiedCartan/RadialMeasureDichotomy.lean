import ModifiedCartan.RadialAnchors

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- If the common good set is too small, one of finitely many bad sets has
positive prescribed outer measure. No measurability hypotheses are needed. -/
theorem exists_large_component_of_small_complement {ι : Type*} [Fintype ι] (S : Set ℝ) (E : ι → Set ℝ)
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 ≤ θ)
    (hgood : volume (S \ ⋃ i, E i) ≤ ENNReal.ofReal ε)
    (hsize : ENNReal.ofReal (ε+(Fintype.card ι : ℝ)*θ) < volume S) :
    ∃ i, ENNReal.ofReal θ < volume (E i) := by
  by_contra hn
  push Not at hn
  have hcover : S ⊆ (S \ ⋃ i, E i) ∪ ⋃ i, E i := by
    intro r hr
    by_cases he : r ∈ ⋃ i, E i
    · exact Or.inr he
    · exact Or.inl ⟨hr,he⟩
  have hsum : (∑ i, volume (E i)) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ)*θ) := by
    calc
      _ ≤ ∑ _i : ι, ENNReal.ofReal θ := Finset.sum_le_sum (fun i _ => hn i)
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun (_i : ι) _ => hθ)]
        simp
  have hbound : volume S ≤ ENNReal.ofReal (ε+(Fintype.card ι : ℝ)*θ) := by
    calc
      _ ≤ volume (S \ ⋃ i, E i)+volume (⋃ i, E i) := (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal ε+ENNReal.ofReal ((Fintype.card ι : ℝ)*θ) :=
        add_le_add hgood ((measure_iUnion_fintype_le volume E).trans hsum)
      _ = _ := (ENNReal.ofReal_add hε (mul_nonneg (Nat.cast_nonneg _) hθ)).symm
  exact (not_lt_of_ge hbound) hsize

/-- A fixed quantitative choice for a finite family of bad-radius sets. -/
theorem exists_large_component_on_interval {ι : Type*} [Fintype ι] (E : ι → Set ℝ) {b c : ℝ}
    (hbc : b < c) (hgood : volume (Icc b c \ ⋃ i, E i) ≤ ENNReal.ofReal ((c-b)/2)) :
    ∃ i, ENNReal.ofReal ((c-b)/(2*((Fintype.card ι : ℝ)+1))) < volume (E i) := by
  have hθ : 0 < (c-b)/(2*((Fintype.card ι : ℝ)+1)) := div_pos (sub_pos.mpr hbc) (by positivity)
  apply exists_large_component_of_small_complement (Icc b c) E (by linarith) hθ.le hgood
  rw [Real.volume_Icc]
  apply (ENNReal.ofReal_lt_ofReal_iff (sub_pos.mpr hbc)).mpr
  have he : ((Fintype.card ι : ℝ)+1)*((c-b)/(2*((Fintype.card ι : ℝ)+1))) = (c-b)/2 := by field_simp
  nlinarith

end ModifiedCartan
