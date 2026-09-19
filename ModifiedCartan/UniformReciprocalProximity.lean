import ModifiedCartan.ReciprocalProximity

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- The reciprocal mean estimate has a radius-independent coefficient when
all anchors remain in a fixed smaller disk. Boundary zeros are permitted. -/
theorem proximityMean_inv_le_uniform_anchor {f : ℂ → ℂ} {a b R B : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hbR : b ≤ R) (hR : R ≤ 1) (hB : 0 ≤ B)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hanchor : ∃ w : ℂ, ‖w‖ ≤ a ∧ f w ≠ 0 ∧ -B ≤ Real.log ‖f w‖) :
    proximityMean (fun z => (f z)⁻¹) R ≤
      ((1+a)/(b-a))^2*proximityMean f R + (1+a)/(b-a)*B := by
  have hbase := proximityMean_inv_le_of_anchor ha (hab.trans_le hbR) hB hf hanchor
  have hq0 : 0 ≤ (R+a)/(R-a) := div_nonneg (by linarith) (by linarith)
  have hq : (R+a)/(R-a) ≤ (1+a)/(b-a) := by
    apply (div_le_div_iff₀ (by linarith : 0 < R-a) (by linarith : 0 < b-a)).mpr
    exact (mul_le_mul_of_nonneg_left (by linarith : b-a ≤ R-a) (by linarith : 0 ≤ R+a)).trans
      (mul_le_mul_of_nonneg_right (by linarith : R+a ≤ 1+a) (by linarith : 0 ≤ R-a))
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq 2) (ValueDistribution.proximity_nonneg R))
    (mul_le_mul_of_nonneg_right hq hB))

theorem proximityMean_inv_growth_bound {a b A B : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℂ) (R M : ℝ),
      b ≤ R → R ≤ 1 → 1 ≤ M →
      AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) →
      proximityMean f R ≤ B*(Real.log M+1) →
      (∃ w : ℂ, ‖w‖ ≤ a ∧ f w ≠ 0 ∧ -A*(Real.log M+1) ≤ Real.log ‖f w‖) →
      proximityMean (fun z => (f z)⁻¹) R ≤ C*(Real.log M+1) := by
  let Q := (1+a)/(b-a)
  have hQ : 0 ≤ Q := div_nonneg (by linarith) (by linarith)
  refine ⟨Q^2*B+Q*A, add_nonneg (mul_nonneg (sq_nonneg _) hB) (mul_nonneg hQ hA), ?_⟩
  intro f R M hbR hR hM hf hm haF
  have hL : 0 ≤ Real.log M+1 := by linarith [Real.log_nonneg hM]
  have hbase := proximityMean_inv_le_uniform_anchor ha hab hbR hR (mul_nonneg hA hL) hf
    (by simpa only [neg_mul] using haF)
  change proximityMean (fun z => (f z)⁻¹) R ≤ Q^2*proximityMean f R+Q*(A*(Real.log M+1)) at hbase
  calc
    _ ≤ Q^2*proximityMean f R+Q*(A*(Real.log M+1)) := hbase
    _ ≤ Q^2*(B*(Real.log M+1))+Q*(A*(Real.log M+1)) :=
      add_le_add (mul_le_mul_of_nonneg_left hm (sq_nonneg Q)) (le_refl _)
    _ = (Q^2*B+Q*A)*(Real.log M+1) := by ring

end ModifiedCartan
