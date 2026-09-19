import ModifiedCartan.DerivedFractionRadii
import ModifiedCartan.WronskianAnchorGrowth

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

theorem wronskian_three_growth_of_small_good_set {a b c T R r₀ η τ : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c) (haT : a < T) (hcT : c < T)
    (hTR : T < R) (hRr : R < r₀) (hr1 : r₀ < 1)
    (hη : 0 < η) (hηr : η < r₀) (hτ : 0 < τ) :
    ∃ D C : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ ∀ (g : Fin 3 → ℂ → ℂ) (r s M : ℝ),
      (∀ j, IsHolomorphicUnit (g j) (disk 1)) →
      r₀ ≤ r → r < s → s < 1 → 1 ≤ M → s-r = 1/M →
      (∀ i j, τ ≤ diskSupNorm (fun z => g i z/g j z) η) →
      (∀ i j, proximityMean (fun z => g i z/g j z) s ≤ 2*M) →
      (∀ i j, i ≠ j → ∃ w : ℂ, ‖w‖ ≤ a ∧ 1 ≤ ‖normalizedWronskian ![g i,g j] w‖) →
      volume (radialCommonGoodSet (fun σ : Equiv.Perm (Fin 3) => thirdDerivedFraction (g ∘ σ)) b c)
        ≤ ENNReal.ofReal ((c-b)/2) →
      (∃ w : ℂ, ‖w‖ ≤ c ∧ normalizedWronskian g w ≠ 0 ∧
        -D*(Real.log M+1) ≤ Real.log ‖normalizedWronskian g w‖) ∧
      proximityMean (fun z => (normalizedWronskian g z)⁻¹) r ≤ C*(Real.log M+1) := by
  let δ := (c-b)/(2*((Fintype.card (Equiv.Perm (Fin 3)) : ℝ)+1))
  have hδ : 0 < δ := div_pos (sub_pos.mpr hbc) (by positivity)
  obtain ⟨D,C,hD,hC,hbound⟩ := wronskian_three_anchor_and_reciprocal_growth
    ha hb hbc haT hcT hTR hRr hr1 hδ hη hηr hτ
  refine ⟨D,C,hD,hC,?_⟩
  intro g r s M hg hr hrs hs hM hgap hsup hmeans ha hgood
  obtain ⟨σ,hσ⟩ := exists_large_orientation
    (fun σ : Equiv.Perm (Fin 3) => thirdDerivedFraction (g ∘ σ)) hbc hgood
  let S := radialLargeValueSet (thirdDerivedFraction (g ∘ σ)) b c
  have hh := hbound (g ∘ σ) r s M S (fun j => hg (σ j)) hr hrs hs hM hgap
    (fun j => hsup (σ j) (σ 0)) (fun j => hmeans (σ j) (σ 0))
    (fun _ hx => hx.1) hσ.le
    (ha (σ 0) (σ 1) (σ.injective.ne (by decide)))
    (ha (σ 0) (σ 2) (σ.injective.ne (by decide))) (fun _ hx => hx.2)
  constructor
  · obtain ⟨w,hw,hn,hl⟩ := hh.1
    have he := normalizedWronskian_norm_comp_perm g σ w
    refine ⟨w,hw,?_,by simpa only [he] using hl⟩
    apply norm_ne_zero_iff.mp
    rw [← he]
    exact norm_ne_zero_iff.mpr hn
  · simpa only [normalizedWronskian_inv_proximity_comp_perm] using hh.2

theorem wronskian_four_growth_of_small_good_set {a b c T R r₀ η τ A : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c) (haT : a < T) (hcT : c < T)
    (hTR : T < R) (hRr : R < r₀) (hr1 : r₀ < 1)
    (hη : 0 < η) (hηr : η < r₀) (hτ : 0 < τ) (hA : 0 ≤ A) :
    ∃ D C : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ ∀ (g : Fin 4 → ℂ → ℂ) (r s M : ℝ),
      (∀ j, IsHolomorphicUnit (g j) (disk 1)) →
      r₀ ≤ r → r < s → s < 1 → 1 ≤ M → s-r = 1/M →
      (∀ i j, τ ≤ diskSupNorm (fun z => g i z/g j z) η) →
      (∀ i j, proximityMean (fun z => g i z/g j z) s ≤ 2*M) →
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∃ w : ℂ, ‖w‖ ≤ a ∧
        normalizedWronskian ![g i,g j,g k] w ≠ 0 ∧
        -A*(Real.log M+1) ≤ Real.log ‖normalizedWronskian ![g i,g j,g k] w‖) →
      volume (radialCommonGoodSet (fun σ : Equiv.Perm (Fin 4) => fourthDerivedFraction (g ∘ σ)) b c)
        ≤ ENNReal.ofReal ((c-b)/2) →
      (∃ w : ℂ, ‖w‖ ≤ c ∧ normalizedWronskian g w ≠ 0 ∧
        -D*(Real.log M+1) ≤ Real.log ‖normalizedWronskian g w‖) ∧
      proximityMean (fun z => (normalizedWronskian g z)⁻¹) r ≤ C*(Real.log M+1) := by
  let δ := (c-b)/(2*((Fintype.card (Equiv.Perm (Fin 4)) : ℝ)+1))
  have hδ : 0 < δ := div_pos (sub_pos.mpr hbc) (by positivity)
  obtain ⟨D,C,hD,hC,hbound⟩ := wronskian_four_anchor_and_reciprocal_growth
    ha hb hbc haT hcT hTR hRr hr1 hδ hη hηr hτ hA
  refine ⟨D,C,hD,hC,?_⟩
  intro g r s M hg hr hrs hs hM hgap hsup hmeans ha hgood
  obtain ⟨σ,hσ⟩ := exists_large_orientation
    (fun σ : Equiv.Perm (Fin 4) => fourthDerivedFraction (g ∘ σ)) hbc hgood
  let S := radialLargeValueSet (fourthDerivedFraction (g ∘ σ)) b c
  have hh := hbound (g ∘ σ) r s M S (fun j => hg (σ j)) hr hrs hs hM hgap
    (fun j => hsup (σ j) (σ 0)) (fun j => hmeans (σ j) (σ 0))
    (fun _ hx => hx.1) hσ.le
    (ha (σ 0) (σ 1) (σ 2) (σ.injective.ne (by decide))
      (σ.injective.ne (by decide)) (σ.injective.ne (by decide)))
    (ha (σ 0) (σ 1) (σ 3) (σ.injective.ne (by decide))
      (σ.injective.ne (by decide)) (σ.injective.ne (by decide))) (fun _ hx => hx.2)
  constructor
  · obtain ⟨w,hw,hn,hl⟩ := hh.1
    have he := normalizedWronskian_norm_comp_perm g σ w
    refine ⟨w,hw,?_,by simpa only [he] using hl⟩
    apply norm_ne_zero_iff.mp
    rw [← he]
    exact norm_ne_zero_iff.mpr hn
  · simpa only [normalizedWronskian_inv_proximity_comp_perm] using hh.2

end ModifiedCartan
