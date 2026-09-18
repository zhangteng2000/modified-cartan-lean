import ModifiedCartan.IteratedLogDerivativeMean
import ModifiedCartan.DerivativeQuotientRecurrence

noncomputable section
set_option autoImplicit false
open Filter Metric Set Real
namespace ModifiedCartan

theorem proximityMean_self_div (F : ℂ → ℂ) (r : ℝ) :
    proximityMean (fun z => F z / F z) r = 0 := by
  have he : (fun z => Real.posLog ‖F z / F z‖) = (fun _ : ℂ => (0 : ℝ)) := by
    ext z
    by_cases hz : F z = 0 <;> simp [hz]
  simp only [proximityMean, ValueDistribution.proximity_top, he, Real.circleAverage_const]

theorem higher_derivative_quotient_mean {α r₀ : ℝ} (hα : 0 < α) (hαr : α < r₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℂ → ℂ) (τ r R : ℝ),
      DifferentiableOn ℂ F (disk 1) → 0 < τ → τ ≤ diskSupNorm F α →
      r₀ ≤ r → r < R → R < 1 →
      proximityMean (fun z => iteratedDeriv k F z / F z) r ≤
        C * (Real.log (2 + proximityMean F R + Real.posLog (1 / τ)) + Real.log (1 / (R - r))) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro F τ r R _hF _hτ _hτF _hr₀ _hrR _hR
      simp [proximityMean_self_div]
    | succ n =>
      choose Q hQ hQbound using fun i : Fin (n + 1) => ih i i.isLt
      choose L hL hLbound using fun i : Fin (n + 1) => iterated_log_derivative_mean hα hαr i
      let M := (∑ i : Fin (n + 1), Q i) + (∑ i : Fin (n + 1), L i)
      let A := (∑ i ∈ Finset.range (n + 1), Real.posLog (n.choose i : ℝ)) + Real.posLog (n + 1 : ℝ)
      have hM : 0 ≤ M := add_nonneg (Finset.sum_nonneg (fun i _ => hQ i))
        (Finset.sum_nonneg (fun i _ => hL i))
      have hA : 0 ≤ A := add_nonneg (Finset.sum_nonneg (fun _ _ => Real.posLog_nonneg)) Real.posLog_nonneg
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      refine ⟨A / Real.log 2 + (n + 1 : ℝ) * M, by positivity, ?_⟩
      intro F τ r R hF hτ hτF hr₀ hrR hR
      let E := Real.log (2 + proximityMean F R + Real.posLog (1 / τ)) + Real.log (1 / (R - r))
      have hr : 0 < r := hα.trans (hαr.trans_le hr₀)
      have hm : 0 ≤ proximityMean F R := ValueDistribution.proximity_nonneg R
      have hP : 0 ≤ Real.posLog (1 / τ) := Real.posLog_nonneg
      have hb : 2 ≤ 2 + proximityMean F R + Real.posLog (1 / τ) := by linarith
      have ht : 1 ≤ 1 / (R - r) := (le_div_iff₀ (sub_pos.mpr hrR)).mpr (by linarith)
      have hElower : Real.log 2 ≤ E := by
        have hl := Real.log_le_log (by norm_num : (0:ℝ) < 2) hb
        have htlog := Real.log_nonneg ht
        dsimp [E]
        linarith
      have hE : 0 ≤ E := hlog2.le.trans hElower
      have hprevious : ∀ j : ℕ, j ≤ n →
          proximityMean (fun z => iteratedDeriv j F z / F z) r ≤ (∑ i : Fin (n + 1), Q i) * E := by
        intro j hj
        apply (hQbound ⟨j, by omega⟩ F τ r R hF hτ hτF hr₀ hrR hR).trans
        apply mul_le_mul_of_nonneg_right _ hE
        exact Finset.single_le_sum (fun i _ => hQ i) (Finset.mem_univ _)
      have hlogs : ∀ j : ℕ, j ≤ n → proximityMean (iteratedDeriv j (logDeriv F)) r ≤
          (∑ i : Fin (n + 1), L i) * E := by
        intro j hj
        apply (hLbound ⟨j, by omega⟩ F τ r R hF hτ hτF hr₀ hrR hR).trans
        apply mul_le_mul_of_nonneg_right _ hE
        exact Finset.single_le_sum (fun i _ => hL i) (Finset.mem_univ _)
      have hα1 : α < 1 := hαr.trans_le hr₀ |>.trans (hrR.trans hR)
      obtain ⟨w, hw, hmax⟩ := diskSupNorm_attained hα.le
        (hF.continuousOn.mono (closedBall_subset_ball hα1))
      have hFw : F w ≠ 0 := norm_pos_iff.mp (hτ.trans_le (by rwa [← hmax]))
      have hrec := derivative_quotient_proximity_recurrence hF hr (hrR.trans hR)
        (closedBall_subset_ball hα1 hw) hFw n
      have hsum : (∑ i ∈ Finset.range (n + 1),
          (Real.posLog (n.choose i : ℝ) + proximityMean (iteratedDeriv i (logDeriv F)) r +
            proximityMean (fun z => iteratedDeriv (n - i) F z / F z) r)) ≤
          (∑ i ∈ Finset.range (n + 1), Real.posLog (n.choose i : ℝ)) + (n + 1 : ℝ) * M * E := by
        calc
          _ ≤ ∑ i ∈ Finset.range (n + 1), (Real.posLog (n.choose i : ℝ) + M * E) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' : i ≤ n := by simpa using Finset.mem_range.mp hi
            have h1 := hlogs i hi'
            have h2 := hprevious (n - i) (Nat.sub_le _ _)
            dsimp [M]
            nlinarith only [h1, h2]
          _ = _ := by simp [Finset.sum_add_distrib, mul_assoc]
      have hconstant : A ≤ (A / Real.log 2) * E := by
        calc
          _ = (A / Real.log 2) * Real.log 2 := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hElower (div_nonneg hA hlog2.le)
      have hlognat : Real.log (n + 1 : ℝ) ≤ Real.posLog (n + 1 : ℝ) := by
        simp [Real.posLog_apply]
      apply hrec.trans
      dsimp [A] at hconstant
      nlinarith only [hsum, hconstant, hlognat]

/-- Full original manuscript lemma, with no zero-free hypothesis on h. -/
theorem logDerivativeEstimate_proved : LogDerivativeEstimate := by
  intro α rMinus rPlus k hα hαminus _hminusplus hplus _hk
  obtain ⟨C, _hC, hbound⟩ := higher_derivative_quotient_mean hα hαminus k
  refine ⟨C, ?_⟩
  intro h τ r R hh hτ hτh hr hrR hR
  exact hbound h τ r R hh hτ hτh hr hrR (hR.trans_lt hplus)

end ModifiedCartan
