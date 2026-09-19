import ModifiedCartan.UniformReciprocalProximity
import ModifiedCartan.QuotientGrowth

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- Either orientation of a unit quotient controls both proximity means,
provided each orientation has an anchor in one fixed smaller disk. -/
theorem unit_proximity_pair_balance {f : ℂ → ℂ} {a b R A L : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hbR : b ≤ R) (hR1 : R < 1)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hf : IsHolomorphicUnit f (disk 1))
    (haF : ∃ w : ℂ, ‖w‖ ≤ a ∧ f w ≠ 0 ∧ -A ≤ Real.log ‖f w‖)
    (haInv : ∃ w : ℂ, ‖w‖ ≤ a ∧ (f w)⁻¹ ≠ 0 ∧ -A ≤ Real.log ‖(f w)⁻¹‖)
    (hbound : proximityMean f R ≤ L ∨ proximityMean (fun z => (f z)⁻¹) R ≤ L) :
    proximityMean f R+proximityMean (fun z => (f z)⁻¹) R ≤
      (1+((1+a)/(b-a))^2)*L+(1+a)/(b-a)*A := by
  let Q := (1+a)/(b-a)
  have hsub : closedBall (0 : ℂ) R ⊆ disk 1 := closedBall_subset_ball hR1
  have hfa := hf.1.analyticOnNhd isOpen_ball
  have hia : AnalyticOnNhd ℂ (fun z => (f z)⁻¹) (disk 1) := fun z hz => (hfa z hz).inv (hf.2 z hz)
  have h1 := proximityMean_inv_le_uniform_anchor ha hab hbR hR1.le hA (hfa.mono hsub) haF
  have h2 := proximityMean_inv_le_uniform_anchor ha hab hbR hR1.le hA (hia.mono hsub) haInv
  simp only [inv_inv] at h2
  change proximityMean (fun z => (f z)⁻¹) R ≤ Q^2*proximityMean f R+Q*A at h1
  change proximityMean f R ≤ Q^2*proximityMean (fun z => (f z)⁻¹) R+Q*A at h2
  change proximityMean f R+proximityMean (fun z => (f z)⁻¹) R ≤ (1+Q^2)*L+Q*A
  rcases hbound with hb | hb
  · have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg Q)
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg Q)
    nlinarith

end ModifiedCartan
