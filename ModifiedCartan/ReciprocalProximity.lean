import ModifiedCartan.LogPoisson
import ModifiedCartan.ProximityLocal

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- Local-circle version of the difference of the two proximity means. -/
theorem proximityMean_sub_inv {f : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (sphere (0 : ℂ) |R|)) :
    proximityMean f R - proximityMean (fun z => (f z)⁻¹) R =
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 R := by
  unfold proximityMean
  simp only [ValueDistribution.proximity_top]
  have hi : CircleIntegrable (fun z => Real.posLog ‖(f z)⁻¹‖) 0 R := by
    simpa only [Pi.inv_apply] using hf.inv.circleIntegrable_posLog_norm
  rw [← Real.circleAverage_sub hf.circleIntegrable_posLog_norm hi]
  congr 1
  ext z
  simp only [Pi.sub_apply, norm_inv, Real.posLog_sub_posLog_inv]

/-- A nonzero interior anchor controls the reciprocal proximity; zeros on the
integration circle are allowed. -/
theorem proximityMean_inv_le {f : ℂ → ℂ} {R : ℝ} {w : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hw : w ∈ ball (0 : ℂ) R) (hne : f w ≠ 0) :
    let q := (R + ‖w‖) / (R - ‖w‖)
    proximityMean (fun z => (f z)⁻¹) R ≤ q^2 * proximityMean f R - q * Real.log ‖f w‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hm : MeromorphicOn f (sphere (0 : ℂ) |R|) := by
    simpa only [abs_of_pos hR] using (hf.mono sphere_subset_closedBall).meromorphicOn
  have h := poisson_mean_inequality hf hw hne
  rw [← proximityMean_sub_inv hm] at h
  dsimp only at h ⊢
  nlinarith

/-- Uniform form for moving anchors in a fixed smaller disk. -/
theorem proximityMean_inv_le_of_anchor {f : ℂ → ℂ} {a R B : ℝ}
    (ha : 0 ≤ a) (haR : a < R) (hB : 0 ≤ B)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hanchor : ∃ w : ℂ, ‖w‖ ≤ a ∧ f w ≠ 0 ∧ -B ≤ Real.log ‖f w‖) :
    proximityMean (fun z => (f z)⁻¹) R ≤
      ((R+a)/(R-a))^2 * proximityMean f R + (R+a)/(R-a) * B := by
  obtain ⟨w, hw, hn, hlog⟩ := hanchor
  have hwR : w ∈ ball (0 : ℂ) R := by simpa using hw.trans_lt haR
  have hb := proximityMean_inv_le hf hwR hn
  let q := (R+‖w‖)/(R-‖w‖)
  let Q := (R+a)/(R-a)
  have hq0 : 0 ≤ q := div_nonneg (by linarith [norm_nonneg w]) (by linarith)
  have hqQ : q ≤ Q := by
    apply (div_le_div_iff₀ (by linarith : 0 < R-‖w‖) (by linarith : 0 < R-a)).mpr
    have hR : 0 ≤ R := ha.trans haR.le
    nlinarith
  have hs : q^2 ≤ Q^2 := pow_le_pow_left₀ hq0 hqQ 2
  have hm : 0 ≤ proximityMean f R := ValueDistribution.proximity_nonneg R
  have h1 := mul_le_mul_of_nonneg_right hs hm
  have h2 := mul_le_mul_of_nonneg_left hlog hq0
  have h3 := mul_le_mul_of_nonneg_right hqQ hB
  change proximityMean (fun z => (f z)⁻¹) R ≤ q^2 * proximityMean f R - q * Real.log ‖f w‖ at hb
  change proximityMean (fun z => (f z)⁻¹) R ≤ Q^2 * proximityMean f R + Q * B
  linarith

end ModifiedCartan
