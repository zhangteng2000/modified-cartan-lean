import ModifiedCartan.NormalizedWronskian
import ModifiedCartan.CartanBoundedPairs

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

theorem normalizedWronskian_two_norm {f g : ℂ → ℂ} {z : ℂ}
    (hf : f z ≠ 0) (hg : g z ≠ 0)
    (hdf : DifferentiableAt ℂ f z) (hdg : DifferentiableAt ℂ g z) :
    ‖normalizedWronskian ![f,g] z‖ = ‖logDeriv (fun w => f w/g w) z‖ := by
  rw [normalizedWronskian_two hf hg,logDeriv_div z hf hg hdf hdg]
  exact norm_sub_rev _ _

/-- Failure of the bounded-pair case supplies a genuine inner Wronskian anchor. -/
theorem pair_anchor_of_not_logDerivative_bound {f g : ℂ → ℂ} {T : ℝ}
    (hf : IsHolomorphicUnit f (disk T)) (hg : IsHolomorphicUnit g (disk T))
    (hnot : ¬ ∀ z ∈ disk T, ‖logDeriv (fun w => f w/g w) z‖ ≤ 1) :
    ∃ w : ℂ, ‖w‖ ≤ T ∧ 1 ≤ ‖normalizedWronskian ![f,g] w‖ := by
  push_neg at hnot
  obtain ⟨w,hw,hb⟩ := hnot
  refine ⟨w,(show ‖w‖ < T by simpa [disk] using hw).le,?_⟩
  rw [normalizedWronskian_two_norm (hf.2 w hw) (hg.2 w hw)
    (hf.1.differentiableAt (isOpen_ball.mem_nhds hw))
    (hg.1.differentiableAt (isOpen_ball.mem_nhds hw))]
  exact hb.le

end ModifiedCartan
