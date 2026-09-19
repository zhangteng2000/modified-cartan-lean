import ModifiedCartan.UnitProximityBalance
import ModifiedCartan.NormalizedWronskianGrowth
import ModifiedCartan.QuotientAnchors
import ModifiedCartan.WronskianQuotients

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- A bounded three-term derived fraction for every pair controls the whole
pairwise growth on that circle. Pair Wronskians have genuine inner anchors;
no reciprocal proximity bound is supplied as a premise. -/
theorem pairGrowth_bound_of_small_three_fractions {η a r₀ A : ℝ}
    (hη : 0 < η) (ha : 0 ≤ a) (hηr : η < r₀) (har : a < r₀)
    (hr1 : r₀ < 1) (hA : 0 ≤ A) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fin p → ℂ → ℂ) (r s M : ℝ),
      (∀ i, IsHolomorphicUnit (f i) (disk 1)) →
      r₀ ≤ r → r < s → s < 1 → 1 ≤ M → s-r = 1/M → pairGrowthMean f s ≤ 2*M →
      (∀ i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧ -A ≤ Real.log ‖f i w/f j w‖) →
      (∀ i j, i ≠ j → ∃ w : ℂ, ‖w‖ ≤ a ∧ 1 ≤ ‖normalizedWronskian ![f i,f j] w‖) →
      (∀ i j, i ≠ j → ∀ z ∈ sphere (0 : ℂ) r, wronskian ![f i,f j] z ≠ 0) →
      (∀ i j, i ≠ j → ∃ k : Fin p, k ≠ i ∧ k ≠ j ∧ ∀ z ∈ sphere (0 : ℂ) r,
        ‖f k z*wronskian ![f k,f i,f j] z/(wronskian ![f k,f i] z*wronskian ![f k,f j] z)‖ ≤ 1) →
      pairGrowthMean f r ≤ C*(Real.log M+1) := by
  obtain ⟨B,hB,hbound⟩ := normalizedWronskian_growth_bound hη hηr (Real.exp_pos (-A)) 2
  obtain ⟨V,hV,hinv⟩ := proximityMean_inv_growth_bound ha har (by norm_num : (0 : ℝ) ≤ 0) hB
  let T := 2*Real.pi+B+V
  let Q := (1+η)/(r₀-η)
  let P := (1+Q^2)*T+Q*A
  let C := 1+(p : ℝ)*(p : ℝ)*P
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hQ : 0 ≤ Q := div_nonneg (by linarith) (by linarith)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro f r s M hf hr hrs hs hM hgap hMs hanchors hWanchors hWcircle hfractions
  let ℓ := Real.log M+1
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith [Real.log_nonneg hM]
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hr0 : 0 < r := hη.trans (hηr.trans_le hr)
  have hr' : r < 1 := hrs.trans hs
  have hunit (i j : Fin p) : ∀ k : Fin 2, IsHolomorphicUnit (![f i,f j] k) (disk 1) := by
    intro k
    fin_cases k <;> simpa using hf _
  have hpair (i j : Fin p) : proximityMean (normalizedWronskian ![f i,f j]) r ≤ B*ℓ := by
    apply hbound ![f i,f j] (f i) r s M (hunit i j) (hf i)
    · intro k
      fin_cases k <;> simpa using diskSupNorm_ge_exp_of_log_anchor (hηr.trans hr1)
        (unit_quotient (hf _) (hf i)) (hanchors _ i)
    · exact hr
    · exact hrs
    · exact hs
    · exact hM
    · exact hgap
    · intro k
      fin_cases k <;> simpa using (quotient_proximity_le_pairGrowthMean f _ i s).trans hMs
  have hpairInv (i j : Fin p) (hij : i ≠ j) :
      proximityMean (fun z => (normalizedWronskian ![f i,f j] z)⁻¹) r ≤ V*ℓ := by
    apply hinv (normalizedWronskian ![f i,f j]) r M hr hr'.le hM
      ((normalizedWronskian_analyticOnNhd
        (fun k => (hunit i j k).1.analyticOnNhd isOpen_ball) (fun k => (hunit i j k).2)).mono
        (closedBall_subset_ball hr')) (hpair i j)
    obtain ⟨w,hw,hn⟩ := hWanchors i j hij
    exact ⟨w,hw,norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hn),
      by simpa using Real.log_nonneg hn⟩
  have hsub : sphere (0 : ℂ) |r| ⊆ disk 1 := by
    rw [abs_of_pos hr0]
    exact sphere_subset_ball hr'
  have hpairs : ∀ i j, proximityMean (fun z => f i z/f j z) r ≤ P*ℓ := by
    intro i j
    by_cases hij : i = j
    · subst j
      have he : EqOn (fun z => f i z/f i z) (fun _ => 1) (sphere (0 : ℂ) |r|) :=
        fun z hz => div_self ((hf i).2 z (hsub hz))
      rw [proximityMean_congr_circle he]
      simpa [proximityMean,ValueDistribution.proximity_const] using mul_nonneg hP hℓ0
    obtain ⟨k,hki,hkj,hd⟩ := hfractions i j hij
    have hc := wronskian_three_circle_proximity_alternative hr0 hr' (by norm_num : (0 : ℝ) ≤ 1)
      (g := ![f k,f i,f j]) (by intro l; fin_cases l <;> simpa using hf _)
      (by simpa using hWcircle k i hki) (by simpa using hWcircle k j hkj)
      (by simpa using hd)
    have hπ : 2*Real.pi*r ≤ 2*Real.pi*ℓ :=
      mul_le_mul_of_nonneg_left (hr'.le.trans hℓ) (by positivity)
    have halter : proximityMean (fun z => f i z/f j z) r ≤ T*ℓ ∨
        proximityMean (fun z => (f i z/f j z)⁻¹) r ≤ T*ℓ := by
      rcases hc with hc | hc
      · left
        have h1 := hpair k j
        have h2 := hpairInv k i hki
        change proximityMean (fun z => f i z/f j z) r ≤ 2*Real.pi*r*1+
          proximityMean (normalizedWronskian ![f k,f j]) r+
          proximityMean (fun z => (normalizedWronskian ![f k,f i] z)⁻¹) r at hc
        dsimp [T]
        nlinarith
      · right
        simp only [inv_div]
        have h1 := hpair k i
        have h2 := hpairInv k j hkj
        change proximityMean (fun z => f j z/f i z) r ≤ 2*Real.pi*r*1+
          proximityMean (normalizedWronskian ![f k,f i]) r+
          proximityMean (fun z => (normalizedWronskian ![f k,f j] z)⁻¹) r at hc
        dsimp [T]
        nlinarith
    have hanchor' (i j : Fin p) : ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧
        -(A*ℓ) ≤ Real.log ‖f i w/f j w‖ := by
      obtain ⟨w,hw,hn,hl⟩ := hanchors i j
      exact ⟨w,hw,hn,by nlinarith⟩
    have hbal := unit_proximity_pair_balance hη.le hηr hr hr' (mul_nonneg hA hℓ0)
      (mul_nonneg hT hℓ0) (unit_quotient (hf i) (hf j)) (hanchor' i j)
      (by simpa only [inv_div] using hanchor' j i) halter
    have he : (1+((1+η)/(r₀-η))^2)*(T*ℓ)+(1+η)/(r₀-η)*(A*ℓ) = P*ℓ := by dsimp [P,Q]; ring
    rw [he] at hbal
    exact (le_add_of_nonneg_right (ValueDistribution.proximity_nonneg r)).trans hbal
  have hsum : (∑ i, ∑ j, proximityMean (fun z => f i z/f j z) r) ≤ (p : ℝ)*(p : ℝ)*P*ℓ := by
    calc
      _ ≤ ∑ _i : Fin p, ∑ _j : Fin p, P*ℓ :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpairs i j))
      _ = _ := by simp [mul_assoc]
  change 1+(∑ i, ∑ j, proximityMean (fun z => f i z/f j z) r) ≤ C*ℓ
  dsimp [C]
  nlinarith

end ModifiedCartan
