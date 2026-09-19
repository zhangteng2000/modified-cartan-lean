import ModifiedCartan.RadialAnchors
import ModifiedCartan.UniformReciprocalProximity

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- The higher-order anchor induction, with all exceptional sets constructed:
large derived fractions on a fixed positive amount of radial length give a
logarithmic reciprocal mean bound for the remaining holomorphic factor. -/
theorem derived_fraction_anchor_and_reciprocal_growth {a b c T R r₀ δ A B : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c) (haT : a < T) (hcT : c < T)
    (hTR : T < R) (hRr : R < r₀) (hr1 : r₀ < 1) (hδ : 0 < δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (m : ℕ) :
    ∃ D C : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ ∀ (F : Fin m → ℂ → ℂ) (G H : ℂ → ℂ) (r M : ℝ) (S : Set ℝ),
      (∀ i, DifferentiableOn ℂ (F i) (disk 1)) →
      DifferentiableOn ℂ G (disk 1) → DifferentiableOn ℂ H (disk 1) →
      r₀ ≤ r → r < 1 → 1 ≤ M → S ⊆ Icc b c → ENNReal.ofReal δ ≤ volume S →
      (∀ i, ∃ w : ℂ, ‖w‖ ≤ a ∧ F i w ≠ 0 ∧ -A*(Real.log M+1) ≤ Real.log ‖F i w‖) →
      (∀ i, proximityMean (F i) r ≤ B*(Real.log M+1)) →
      proximityMean G r ≤ B*(Real.log M+1) → proximityMean H r ≤ B*(Real.log M+1) →
      (∀ ρ ∈ S, ∃ z : ℂ, ‖z‖ = ρ ∧ 1 < ‖G z*H z/(∏ i, F i z)‖) →
      (∃ w : ℂ, ‖w‖ ≤ c ∧ H w ≠ 0 ∧ -D*(Real.log M+1) ≤ Real.log ‖H w‖) ∧
      proximityMean (fun z => (H z)⁻¹) r ≤ C*(Real.log M+1) := by
  have hc : 0 < c := hb.trans_lt hbc
  have hcr : c < r₀ := (hcT.trans hTR).trans hRr
  obtain ⟨K,hK,hsmall⟩ := cartan_small_value_radii_proximity ha hb hbc haT hcT hTR hRr hr1
  let ε := δ/((m : ℝ)+1)
  let L := K*(1+A+B)/ε
  let Q := (1+c)/(r₀-c)
  let D := Q*B+(m : ℝ)*L
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hL : 0 ≤ L := div_nonneg (mul_nonneg hK.le (by linarith)) hε.le
  have hQ : 0 ≤ Q := div_nonneg (by linarith) (by linarith)
  have hD : 0 ≤ D := add_nonneg (mul_nonneg hQ hB) (mul_nonneg (Nat.cast_nonneg _) hL)
  obtain ⟨C,hC,hrecip⟩ := proximityMean_inv_growth_bound hc.le hcr hD hB
  refine ⟨D,C,hD,hC,?_⟩
  intro F G H r M S hF hG hH hr hr' hM hS hsize hanchor hmeans hmeanG hmeanH hratio
  let ℓ := Real.log M+1
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith [Real.log_nonneg hM]
  have hℓ0 : 0 ≤ ℓ := (by norm_num : (0 : ℝ) ≤ 1).trans hℓ
  have hbad : ∀ i, volume (radialSmallValueSet (F i) b c (L*ℓ)) ≤ ENNReal.ofReal ε := by
    intro i
    have hi := hsmall (F i) r (A*ℓ) ε (hF i) hr hr' (mul_nonneg hA hℓ0) hε
      (by simpa only [neg_mul] using hanchor i)
    have hpoly : 1+A*ℓ+proximityMean (F i) r ≤ (1+A+B)*ℓ := by
      have hb' := hmeans i
      change proximityMean (F i) r ≤ B*ℓ at hb'
      nlinarith
    have ht : K*(1+A*ℓ+proximityMean (F i) r)/ε ≤ L*ℓ := by
      calc
        _ ≤ K*((1+A+B)*ℓ)/ε := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hK.le) hε.le
        _ = L*ℓ := by dsimp [L]; ring
    exact (measure_mono (radialSmallValueSet_antitone ht)).trans hi
  have hmass : (m : ℝ)*ε < δ := by
    have he : ((m : ℝ)+1)*ε = δ := by dsimp [ε]; field_simp
    nlinarith
  have havoid : (∑ i, volume (radialSmallValueSet (F i) b c (L*ℓ))) < volume S := by
    calc
      _ ≤ ∑ _i : Fin m, ENNReal.ofReal ε := Finset.sum_le_sum (fun i _ => hbad i)
      _ = ENNReal.ofReal ((m : ℝ)*ε) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun (_i : Fin m) _ => hε.le)]
        simp
      _ < ENNReal.ofReal δ := (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hmass
      _ ≤ volume S := hsize
  have hq : (r+c)/(r-c) ≤ Q := by
    apply (div_le_div_iff₀ (by linarith : 0 < r-c) (by linarith : 0 < r₀-c)).mpr
    exact (mul_le_mul_of_nonneg_left (by linarith : r₀-c ≤ r-c) (by linarith : 0 ≤ r+c)).trans
      (mul_le_mul_of_nonneg_right (by linarith : r+c ≤ 1+c) (by linarith : 0 ≤ r-c))
  have hGupper : ∀ ρ ∈ Icc b c, ∀ z : ℂ, ‖z‖ = ρ → ‖G z‖ ≤ Real.exp (Q*B*ℓ) := by
    intro ρ hρ z hz
    apply (norm_le_exp_proximity_on_closedBall hc.le (hcr.trans_le hr)
      (hG.analyticOnNhd isOpen_ball |>.mono (closedBall_subset_ball hr')) (hz.trans_le hρ.2)).trans
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ Q*proximityMean G r := mul_le_mul_of_nonneg_right hq (ValueDistribution.proximity_nonneg r)
      _ ≤ Q*(B*ℓ) := mul_le_mul_of_nonneg_left hmeanG hQ
      _ = Q*B*ℓ := by ring
  obtain ⟨w,hw,hn,hl⟩ := radial_product_anchor F G H (fun _ => L*ℓ) S hS havoid hGupper hratio
  have haH : ∃ w : ℂ, ‖w‖ ≤ c ∧ H w ≠ 0 ∧ -D*(Real.log M+1) ≤ Real.log ‖H w‖ := by
    refine ⟨w,hw,hn,?_⟩
    have he : -(Q*B*ℓ+∑ _i : Fin m, L*ℓ) = -D*(Real.log M+1) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      dsimp [D,ℓ]
      ring
    rwa [he] at hl
  exact ⟨haH,hrecip H r M hr hr'.le hM
    (hH.analyticOnNhd isOpen_ball |>.mono (closedBall_subset_ball hr')) hmeanH haH⟩

theorem reciprocal_growth_of_large_derived_fraction {a b c T R r₀ δ A B : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c) (haT : a < T) (hcT : c < T)
    (hTR : T < R) (hRr : R < r₀) (hr1 : r₀ < 1) (hδ : 0 < δ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin m → ℂ → ℂ) (G H : ℂ → ℂ) (r M : ℝ) (S : Set ℝ),
      (∀ i, DifferentiableOn ℂ (F i) (disk 1)) →
      DifferentiableOn ℂ G (disk 1) → DifferentiableOn ℂ H (disk 1) →
      r₀ ≤ r → r < 1 → 1 ≤ M → S ⊆ Icc b c → ENNReal.ofReal δ ≤ volume S →
      (∀ i, ∃ w : ℂ, ‖w‖ ≤ a ∧ F i w ≠ 0 ∧ -A*(Real.log M+1) ≤ Real.log ‖F i w‖) →
      (∀ i, proximityMean (F i) r ≤ B*(Real.log M+1)) →
      proximityMean G r ≤ B*(Real.log M+1) → proximityMean H r ≤ B*(Real.log M+1) →
      (∀ ρ ∈ S, ∃ z : ℂ, ‖z‖ = ρ ∧ 1 < ‖G z*H z/(∏ i, F i z)‖) →
      proximityMean (fun z => (H z)⁻¹) r ≤ C*(Real.log M+1) := by
  obtain ⟨D,C,hD,hC,h⟩ := derived_fraction_anchor_and_reciprocal_growth ha hb hbc haT hcT
    hTR hRr hr1 hδ hA hB m
  refine ⟨C,hC,?_⟩
  intro F G H r M S hF hG hH hr hr' hM hS hsize haF hmF hmG hmH hratio
  exact (h F G H r M S hF hG hH hr hr' hM hS hsize haF hmF hmG hmH hratio).2

end ModifiedCartan
