import ModifiedCartan.HolomorphicCancellation

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- Uniform bounds on a neighborhood of each point imply bounds on every
compact subset, with no connectedness assumption. -/
theorem locallyBounded_of_local_bounds {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (h : ∀ z ∈ U, ∃ V : Set ℂ, V ∈ 𝓝 z ∧ ∃ C : ℝ, ∀ n w, w ∈ V → ‖g n w‖ ≤ C) :
    LocallyBounded g U := by
  classical
  intro K hKU hK
  have hex : ∀ z : K, ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ n w, w ∈ ball (z : ℂ) r → ‖g n w‖ ≤ C := by
    intro z
    obtain ⟨V, hV, C, hC⟩ := h z (hKU z.property)
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
    exact ⟨r, hr, C, fun n w hw => hC n w (hrV hw)⟩
  choose r hr C hC using hex
  have hcover : K ⊆ ⋃ z : K, ball (z : ℂ) (r z) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr ⟨z, hz⟩)⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun z : K => ball (z : ℂ) (r z)) (fun _ => isOpen_ball) hcover
  refine ⟨∑ z ∈ T, max (C z) 0, ?_⟩
  intro n w hw
  obtain ⟨z, hzT, hwz⟩ := mem_iUnion₂.mp (hT hw)
  exact (hC z n w hwz).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun t _ => le_max_right (C t) 0) hzT))

/-- Holomorphic local bounds extend across the isolated zeros of a fixed
nontrivial holomorphic function, by the maximum principle on surrounding circles. -/
theorem locallyBounded_extend_zeros {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hh : DifferentiableOn ℂ h U)
    (hne : ∃ z ∈ U, h z ≠ 0) (hg : ∀ n, DifferentiableOn ℂ (g n) U)
    (hb : LocallyBounded g {z ∈ U | h z ≠ 0}) : LocallyBounded g U := by
  apply locallyBounded_of_local_bounds
  intro w hw
  obtain ⟨r, c, hr, hc, hCU, hcircle⟩ := nonzero_surrounding_circle hU hconn hh hne hw
  have hSU : sphere w r ⊆ {z ∈ U | h z ≠ 0} := by
    intro z hz
    exact ⟨hCU (sphere_subset_closedBall hz), norm_pos_iff.mp (hc.trans_le (hcircle z hz))⟩
  obtain ⟨C, hC⟩ := hb (sphere w r) hSU (isCompact_sphere w r)
  refine ⟨ball w r, ball_mem_nhds _ hr, C, ?_⟩
  intro n z hz
  have hgd : DifferentiableOn ℂ (g n) (closure (ball w r)) := by
    rw [closure_ball w hr.ne']
    exact (hg n).mono hCU
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgd.diffContOnCl
    (fun v hv => ?_) (subset_closure hz)
  rw [frontier_ball w hr.ne'] at hv
  exact hC n v hv

/-- Compact convergence to zero extends across the same isolated zeros. -/
theorem compactConvergence_zero_extend_zeros {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hh : DifferentiableOn ℂ h U)
    (hne : ∃ z ∈ U, h z ≠ 0) (hg : ∀ n, DifferentiableOn ℂ (g n) U)
    (hlim : CompactConvergence g (fun _ => 0) {z ∈ U | h z ≠ 0}) :
    CompactConvergence g (fun _ => 0) U := by
  apply (compactConvergence_iff hU).mpr
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro w hw
  obtain ⟨r, c, hr, hc, hCU, hcircle⟩ := nonzero_surrounding_circle hU hconn hh hne hw
  have hSU : sphere w r ⊆ {z ∈ U | h z ≠ 0} := by
    intro z hz
    exact ⟨hCU (sphere_subset_closedBall hz), norm_pos_iff.mp (hc.trans_le (hcircle z hz))⟩
  refine ⟨ball w r, nhdsWithin_le_nhds (ball_mem_nhds _ hr), ?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hlim (sphere w r) hSU (isCompact_sphere w r))
    (ε / 2) (half_pos hε)] with n hn
  have hgd : DifferentiableOn ℂ (g n) (closure (ball w r)) := by
    rw [closure_ball w hr.ne']
    exact (hg n).mono hCU
  intro z hz
  have hnorm : ‖g n z‖ ≤ ε / 2 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgd.diffContOnCl
      (fun v hv => ?_) (subset_closure hz)
    rw [frontier_ball w hr.ne'] at hv
    exact (show ‖g n v‖ < ε / 2 by simpa only [dist_zero_left] using hn v hv).le
  simpa only [dist_zero_left] using hnorm.trans_lt (half_lt_self hε)

theorem cclass_extend_zeros {p : ℕ} {f : Family p} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hh : DifferentiableOn ℂ h U)
    (hne : ∃ z ∈ U, h z ≠ 0) (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    {I : Finset (Fin p)} (hI : IsCClass f I {z ∈ U | h z ≠ 0}) : IsCClass f I U := by
  obtain ⟨k, hk, hb, hsum⟩ := hI
  have hquot := fun j n => (hf j n).1.div (hf k n).1 (hf k n).2
  exact ⟨k, hk, fun j hj => locallyBounded_extend_zeros hU hconn hh hne (hquot j) (hb j hj),
    compactConvergence_zero_extend_zeros hU hconn hh hne
      (fun n => DifferentiableOn.fun_sum (fun j _ => hquot j n)) hsum⟩

end ModifiedCartan
