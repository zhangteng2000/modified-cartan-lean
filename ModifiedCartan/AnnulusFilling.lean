import ModifiedCartan.HolomorphicExtension

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

theorem locallyBounded_fill_disk {g : ℕ → ℂ → ℂ} {V : Set ℂ} {r T : ℝ}
    (hr : 0 < r) (hrT : r < T) (hg : ∀ n, DifferentiableOn ℂ (g n) (disk T))
    (hV : sphere (0 : ℂ) r ⊆ V) (hb : LocallyBounded g V) : LocallyBounded g (disk r) := by
  obtain ⟨C, hC⟩ := hb (sphere (0 : ℂ) r) hV (isCompact_sphere _ _)
  intro K hK _
  refine ⟨C, ?_⟩
  intro n z hz
  have hgd : DifferentiableOn ℂ (g n) (closure (disk r)) := by
    rw [disk, closure_ball 0 hr.ne']
    exact (hg n).mono (closedBall_subset_ball hrT)
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgd.diffContOnCl
    (fun w hw => ?_) (subset_closure (hK hz))
  rw [frontier_ball 0 hr.ne'] at hw
  exact hC n w hw

theorem compactConvergence_zero_fill_disk {g : ℕ → ℂ → ℂ} {V : Set ℂ} {r T : ℝ}
    (hr : 0 < r) (hrT : r < T) (hg : ∀ n, DifferentiableOn ℂ (g n) (disk T))
    (hV : sphere (0 : ℂ) r ⊆ V) (hlim : CompactConvergence g (fun _ => 0) V) :
    CompactConvergence g (fun _ => 0) (disk r) := by
  intro K hK hcompact
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hlim (sphere (0 : ℂ) r) hV (isCompact_sphere _ _))
    (ε / 2) (half_pos hε)] with n hn
  have hgd : DifferentiableOn ℂ (g n) (closure (disk r)) := by
    rw [disk, closure_ball 0 hr.ne']
    exact (hg n).mono (closedBall_subset_ball hrT)
  intro z hz
  have hnorm : ‖g n z‖ ≤ ε / 2 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgd.diffContOnCl
      (fun w hw => ?_) (subset_closure (hK hz))
    rw [frontier_ball 0 hr.ne'] at hw
    exact (show ‖g n w‖ < ε / 2 by simpa only [dist_zero_left] using hn w hw).le
  simpa only [dist_zero_left] using hnorm.trans_lt (half_lt_self hε)

/-- A class proved around a surrounding circle fills its entire interior.
Only the original functions, not the merged functions, must be units inside. -/
theorem cclass_fill_disk {p : ℕ} {f : Family p} {V : Set ℂ} {r T : ℝ}
    (hr : 0 < r) (hrT : r < T) (hf : ∀ j n, IsHolomorphicUnit (f j n) (disk T))
    (hV : sphere (0 : ℂ) r ⊆ V) {I : Finset (Fin p)} (hI : IsCClass f I V) :
    IsCClass f I (disk r) := by
  obtain ⟨k, hk, hb, hsum⟩ := hI
  have hquot := fun j n => (hf j n).1.div (hf k n).1 (hf k n).2
  exact ⟨k, hk, fun j hj => locallyBounded_fill_disk hr hrT (hquot j) hV (hb j hj),
    compactConvergence_zero_fill_disk hr hrT
      (fun n => DifferentiableOn.fun_sum (fun j _ => hquot j n)) hV hsum⟩

end ModifiedCartan
