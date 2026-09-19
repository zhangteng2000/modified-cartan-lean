import ModifiedCartan.UniformWronskianGrowth
import ModifiedCartan.DerivedFractionGrowth
import ModifiedCartan.WronskianFourProximity

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- The actual third-order derived-Wronskian branch: two anchored pair
Wronskians and a large derived fraction force logarithmic reciprocal growth
of the triple Wronskian. All upper means come from the proved derivative bound. -/
theorem wronskian_three_anchor_and_reciprocal_growth {a b c T R r₀ δ η τ : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c) (haT : a < T) (hcT : c < T)
    (hTR : T < R) (hRr : R < r₀) (hr1 : r₀ < 1) (hδ : 0 < δ)
    (hη : 0 < η) (hηr : η < r₀) (hτ : 0 < τ) :
    ∃ D C : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ ∀ (g : Fin 3 → ℂ → ℂ) (r s M : ℝ) (S : Set ℝ),
      (∀ j, IsHolomorphicUnit (g j) (disk 1)) →
      r₀ ≤ r → r < s → s < 1 → 1 ≤ M → s-r = 1/M →
      (∀ j, τ ≤ diskSupNorm (fun z => g j z/g 0 z) η) →
      (∀ j, proximityMean (fun z => g j z/g 0 z) s ≤ 2*M) →
      S ⊆ Icc b c → ENNReal.ofReal δ ≤ volume S →
      (∃ w : ℂ, ‖w‖ ≤ a ∧ 1 ≤ ‖normalizedWronskian ![g 0,g 1] w‖) →
      (∃ w : ℂ, ‖w‖ ≤ a ∧ 1 ≤ ‖normalizedWronskian ![g 0,g 2] w‖) →
      (∀ ρ ∈ S, ∃ z : ℂ, ‖z‖ = ρ ∧
        1 < ‖g 0 z*wronskian g z/(wronskian ![g 0,g 1] z*wronskian ![g 0,g 2] z)‖) →
      (∃ w : ℂ, ‖w‖ ≤ c ∧ normalizedWronskian g w ≠ 0 ∧
        -D*(Real.log M+1) ≤ Real.log ‖normalizedWronskian g w‖) ∧
      proximityMean (fun z => (normalizedWronskian g z)⁻¹) r ≤ C*(Real.log M+1) := by
  obtain ⟨B,hB,hbound⟩ := normalizedWronskian_bounded_order_growth_bound hη hηr hτ 3
  obtain ⟨D,C,hD,hC,hgen⟩ := derived_fraction_anchor_and_reciprocal_growth ha hb hbc haT hcT
    hTR hRr hr1 hδ (by norm_num : (0 : ℝ) ≤ 0) hB 2
  refine ⟨D,C,hD,hC,?_⟩
  intro g r s M S hg hr hrs hs hM hgap hsup hmeans hS hsize h01 h02 hlarge
  let H := normalizedWronskian g
  let F : Fin 2 → ℂ → ℂ := ![normalizedWronskian ![g 0,g 1],normalizedWronskian ![g 0,g 2]]
  have hdiff (k : ℕ) (v : Fin k → ℂ → ℂ) (hv : ∀ j, IsHolomorphicUnit (v j) (disk 1)) :
      DifferentiableOn ℂ (normalizedWronskian v) (disk 1) :=
    (normalizedWronskian_analyticOnNhd (fun j => (hv j).1.analyticOnNhd isOpen_ball)
      (fun j => (hv j).2)).differentiableOn
  have hunit (j : Fin 3) : ∀ i : Fin 2, IsHolomorphicUnit (![g 0,g j] i) (disk 1) := by
    intro i
    fin_cases i <;> simpa using hg _
  have hFm : ∀ i, proximityMean (F i) r ≤ B*(Real.log M+1) := by
    have hp (j : Fin 3) : proximityMean (normalizedWronskian ![g 0,g j]) r ≤ B*(Real.log M+1) := by
      apply hbound 2 (by norm_num) _ (g 0) r s M (hunit j) (hg 0)
        (by intro i; fin_cases i <;> simpa using hsup _) hr hrs hs hM hgap
      intro i
      fin_cases i <;> simpa using hmeans _
    intro i
    fin_cases i <;> simpa [F] using hp _
  have hFa : ∀ i, ∃ w : ℂ, ‖w‖ ≤ a ∧ F i w ≠ 0 ∧ -(0 : ℝ)*(Real.log M+1) ≤ Real.log ‖F i w‖ := by
    intro i
    have hanchor : ∃ w : ℂ, ‖w‖ ≤ a ∧ 1 ≤ ‖F i w‖ := by
      fin_cases i
      · simpa [F] using h01
      · simpa [F] using h02
    obtain ⟨w,hw,hn⟩ := hanchor
    exact ⟨w,hw,norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hn),
      by simpa using Real.log_nonneg hn⟩
  apply hgen F (fun _ => 1) H r M S
    (by intro i; fin_cases i <;> simpa [F] using hdiff 2 _ (hunit _))
    (differentiableOn_const 1) (hdiff 3 g hg) hr (hrs.trans hs) hM hS hsize hFa hFm
  · have hL : 0 ≤ Real.log M+1 := by linarith [Real.log_nonneg hM]
    simpa [proximityMean,ValueDistribution.proximity_const] using mul_nonneg hB hL
  · exact hbound 3 le_rfl g (g 0) r s M hg (hg 0) hsup hr hrs hs hM hgap hmeans
  · intro ρ hρ
    obtain ⟨z,hz,hl⟩ := hlarge ρ hρ
    have hzD : z ∈ disk 1 := by
      have hcz : ‖z‖ < 1 := hz.trans_le (hS hρ).2 |>.trans_lt (hcT.trans (hTR.trans (hRr.trans hr1)))
      simpa [disk] using hcz
    have hn01 : wronskian ![g 0,g 1] z ≠ 0 := by intro hh; norm_num [hh] at hl
    have hn02 : wronskian ![g 0,g 2] z ≠ 0 := by intro hh; norm_num [hh] at hl
    refine ⟨z,hz,?_⟩
    have he := normalizedWronskian_three_factor (fun j => (hg j).2 z hzD) hn01 hn02
    simpa only [F,H,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul,he] using hl


/-- The fourth-order step retains both the constructed logarithmic anchor
and the reciprocal bound. Its numerator pair factor is controlled by the
same proved derivative means as the two denominator triple factors. -/
theorem wronskian_four_anchor_and_reciprocal_growth {a b c T R r₀ δ η τ A : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c) (haT : a < T) (hcT : c < T)
    (hTR : T < R) (hRr : R < r₀) (hr1 : r₀ < 1) (hδ : 0 < δ)
    (hη : 0 < η) (hηr : η < r₀) (hτ : 0 < τ) (hA : 0 ≤ A) :
    ∃ D C : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ ∀ (g : Fin 4 → ℂ → ℂ) (r s M : ℝ) (S : Set ℝ),
      (∀ j, IsHolomorphicUnit (g j) (disk 1)) →
      r₀ ≤ r → r < s → s < 1 → 1 ≤ M → s-r = 1/M →
      (∀ j, τ ≤ diskSupNorm (fun z => g j z/g 0 z) η) →
      (∀ j, proximityMean (fun z => g j z/g 0 z) s ≤ 2*M) →
      S ⊆ Icc b c → ENNReal.ofReal δ ≤ volume S →
      (∃ w : ℂ, ‖w‖ ≤ a ∧ normalizedWronskian ![g 0,g 1,g 2] w ≠ 0 ∧
        -A*(Real.log M+1) ≤ Real.log ‖normalizedWronskian ![g 0,g 1,g 2] w‖) →
      (∃ w : ℂ, ‖w‖ ≤ a ∧ normalizedWronskian ![g 0,g 1,g 3] w ≠ 0 ∧
        -A*(Real.log M+1) ≤ Real.log ‖normalizedWronskian ![g 0,g 1,g 3] w‖) →
      (∀ ρ ∈ S, ∃ z : ℂ, ‖z‖ = ρ ∧
        1 < ‖wronskian ![g 0,g 1] z*wronskian g z/
          (wronskian ![g 0,g 1,g 2] z*wronskian ![g 0,g 1,g 3] z)‖) →
      (∃ w : ℂ, ‖w‖ ≤ c ∧ normalizedWronskian g w ≠ 0 ∧
        -D*(Real.log M+1) ≤ Real.log ‖normalizedWronskian g w‖) ∧
      proximityMean (fun z => (normalizedWronskian g z)⁻¹) r ≤ C*(Real.log M+1) := by
  obtain ⟨B,hB,hbound⟩ := normalizedWronskian_bounded_order_growth_bound hη hηr hτ 4
  obtain ⟨D,C,hD,hC,hgen⟩ := derived_fraction_anchor_and_reciprocal_growth ha hb hbc haT hcT
    hTR hRr hr1 hδ hA hB 2
  refine ⟨D,C,hD,hC,?_⟩
  intro g r s M S hg hr hrs hs hM hgap hsup hmeans hS hsize h012 h013 hlarge
  let H := normalizedWronskian g
  let G := normalizedWronskian ![g 0,g 1]
  let F : Fin 2 → ℂ → ℂ := ![normalizedWronskian ![g 0,g 1,g 2],normalizedWronskian ![g 0,g 1,g 3]]
  have hdiff (k : ℕ) (v : Fin k → ℂ → ℂ) (hv : ∀ j, IsHolomorphicUnit (v j) (disk 1)) :
      DifferentiableOn ℂ (normalizedWronskian v) (disk 1) :=
    (normalizedWronskian_analyticOnNhd (fun j => (hv j).1.analyticOnNhd isOpen_ball)
      (fun j => (hv j).2)).differentiableOn
  have hunit (j : Fin 4) : ∀ i : Fin 3, IsHolomorphicUnit (![g 0,g 1,g j] i) (disk 1) := by
    intro i
    fin_cases i <;> simpa using hg _
  have hupair : ∀ i : Fin 2, IsHolomorphicUnit (![g 0,g 1] i) (disk 1) := by
    intro i
    fin_cases i <;> simpa using hg _
  have hFm : ∀ i, proximityMean (F i) r ≤ B*(Real.log M+1) := by
    have hp (j : Fin 4) : proximityMean (normalizedWronskian ![g 0,g 1,g j]) r ≤ B*(Real.log M+1) := by
      apply hbound 3 (by norm_num) _ (g 0) r s M (hunit j) (hg 0)
        (by intro i; fin_cases i <;> simpa using hsup _) hr hrs hs hM hgap
      intro i
      fin_cases i <;> simpa using hmeans _
    intro i
    fin_cases i <;> simpa [F] using hp _
  have hFa : ∀ i, ∃ w : ℂ, ‖w‖ ≤ a ∧ F i w ≠ 0 ∧ -A*(Real.log M+1) ≤ Real.log ‖F i w‖ := by
    intro i
    fin_cases i
    · simpa [F] using h012
    · simpa [F] using h013
  apply hgen F G H r M S
    (by intro i; fin_cases i <;> simpa [F] using hdiff 3 _ (hunit _))
    (hdiff 2 _ hupair) (hdiff 4 g hg) hr (hrs.trans hs) hM hS hsize hFa hFm
  · apply hbound 2 (by norm_num) _ (g 0) r s M hupair (hg 0)
      (by intro i; fin_cases i <;> simpa using hsup _) hr hrs hs hM hgap
    intro i
    fin_cases i <;> simpa using hmeans _
  · exact hbound 4 le_rfl g (g 0) r s M hg (hg 0) hsup hr hrs hs hM hgap hmeans
  · intro ρ hρ
    obtain ⟨z,hz,hl⟩ := hlarge ρ hρ
    have hzD : z ∈ disk 1 := by
      have hcz : ‖z‖ < 1 := hz.trans_le (hS hρ).2 |>.trans_lt (hcT.trans (hTR.trans (hRr.trans hr1)))
      simpa [disk] using hcz
    have hn012 : wronskian ![g 0,g 1,g 2] z ≠ 0 := by intro hh; norm_num [hh] at hl
    have hn013 : wronskian ![g 0,g 1,g 3] z ≠ 0 := by intro hh; norm_num [hh] at hl
    refine ⟨z,hz,?_⟩
    have he := normalizedWronskian_four_factor (fun j => (hg j).2 z hzD) hn012 hn013
    simpa only [F,G,H,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,he] using hl

end ModifiedCartan
