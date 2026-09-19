import ModifiedCartan.UnitProximityBalance
import ModifiedCartan.WronskianQuotients

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- A single logarithmic proximity bound in either orientation of each
pair gives a uniform logarithmic bound for the complete pair growth. -/
theorem pairGrowth_bound_of_proximity_alternatives {η r₀ A B : ℝ}
    (hη : 0 ≤ η) (hηr : η < r₀) (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fin p → ℂ → ℂ) (r M : ℝ),
      (∀ i, IsHolomorphicUnit (f i) (disk 1)) → r₀ ≤ r → r < 1 → 1 ≤ M →
      (∀ i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧ -A ≤ Real.log ‖f i w/f j w‖) →
      (∀ i j, i ≠ j → proximityMean (fun z => f i z/f j z) r ≤ B*(Real.log M+1) ∨
        proximityMean (fun z => f j z/f i z) r ≤ B*(Real.log M+1)) →
      pairGrowthMean f r ≤ C*(Real.log M+1) := by
  let Q := (1+η)/(r₀-η)
  let P := (1+Q^2)*B+Q*A
  let C := 1+(p : ℝ)*(p : ℝ)*P
  have hQ : 0 ≤ Q := div_nonneg (by linarith) (by linarith)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro f r M hf hr hr1 hM hanchors halter
  let ℓ := Real.log M+1
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith [Real.log_nonneg hM]
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hr0 : 0 < r := hη.trans_lt (hηr.trans_le hr)
  have hsub : sphere (0 : ℂ) |r| ⊆ disk 1 := by
    rw [abs_of_pos hr0]
    exact sphere_subset_ball hr1
  have hanchor' (i j : Fin p) : ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧
      -(A*ℓ) ≤ Real.log ‖f i w/f j w‖ := by
    obtain ⟨w,hw,hn,hl⟩ := hanchors i j
    exact ⟨w,hw,hn,by nlinarith⟩
  have hpairs : ∀ i j, proximityMean (fun z => f i z/f j z) r ≤ P*ℓ := by
    intro i j
    by_cases hij : i = j
    · subst j
      have he : EqOn (fun z => f i z/f i z) (fun _ => 1) (sphere (0 : ℂ) |r|) :=
        fun z hz => div_self ((hf i).2 z (hsub hz))
      rw [proximityMean_congr_circle he]
      simpa [proximityMean,ValueDistribution.proximity_const] using mul_nonneg hP hℓ0
    have hbal := unit_proximity_pair_balance hη hηr hr hr1 (mul_nonneg hA hℓ0)
      (mul_nonneg hB hℓ0) (unit_quotient (hf i) (hf j)) (hanchor' i j)
      (by simpa only [inv_div] using hanchor' j i) (by simpa only [inv_div] using halter i j hij)
    have he : (1+((1+η)/(r₀-η))^2)*(B*ℓ)+(1+η)/(r₀-η)*(A*ℓ) = P*ℓ := by dsimp [P,Q]; ring
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
