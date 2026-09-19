import ModifiedCartan.NormalizedWronskian

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- Column replacement bounds each original unit by the reciprocal of the
normalized Wronskian and the exact derivative error. -/
theorem unit_posLog_le_normalizedWronskian_inv {m : ℕ} {g : Fin m → ℂ → ℂ}
    {z : ℂ} {B : ℝ} (hB : 0 ≤ B) (hg : ∀ i, AnalyticAt ℂ (g i) z)
    (hn : ∀ i, g i z ≠ 0)
    (hsum : ∀ k : Fin m, ‖iteratedDeriv (k : ℕ) (fun w => ∑ i, g i w) z‖ ≤ Real.exp B)
    (hW : wronskian g z ≠ 0) (j : Fin m) :
    Real.posLog ‖g j z‖ ≤ Real.posLog ‖(normalizedWronskian g z)⁻¹‖ + wronskianBoundaryError g B z := by
  have hp := wronskian_boundary_log_bound hg hn hn (fun _ => le_rfl) hsum hW j
  have hlog : Real.log ‖normalizedWronskian g z‖ =
      Real.log ‖wronskian g z‖ - ∑ i, Real.log ‖g i z‖ := by
    rw [normalizedWronskian,norm_div,Real.log_div (norm_ne_zero_iff.mpr hW)
      (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hn i))),norm_prod,
      Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (hn i))]
  have hi : -Real.log ‖normalizedWronskian g z‖ ≤ Real.posLog ‖(normalizedWronskian g z)⁻¹‖ := by
    rw [norm_inv,Real.posLog_apply,Real.log_inv]
    exact le_max_right _ _
  rw [Real.posLog_apply]
  apply max_le (add_nonneg Real.posLog_nonneg (wronskianBoundaryError_nonneg g hB z))
  change Real.log ‖wronskian g z‖ ≤ (∑ i, Real.log ‖g i z‖) - Real.log ‖g j z‖ + wronskianBoundaryError g B z at hp
  linarith

/-- Integrated column replacement, allowing every boundary zero of the
Wronskian through the proved codiscrete circle integration theorem. -/
theorem unit_proximity_le_normalizedWronskian_inv {m : ℕ} {g : Fin m → ℂ → ℂ}
    {R B : ℝ} (hR : 0 < R) (hR1 : R < 1) (hB : 0 ≤ B)
    (hg : ∀ i, IsHolomorphicUnit (g i) (disk 1))
    (hW : ∃ z ∈ disk 1, wronskian g z ≠ 0)
    (hsum : ∀ (k : Fin m) z, z ∈ sphere (0 : ℂ) R →
      ‖iteratedDeriv (k : ℕ) (fun w => ∑ i, g i w) z‖ ≤ Real.exp B) (j : Fin m) :
    proximityMean (g j) R ≤ proximityMean (fun z => (normalizedWronskian g z)⁻¹) R +
      Real.circleAverage (wronskianBoundaryError g B) 0 R := by
  have hsub : sphere (0 : ℂ) |R| ⊆ disk 1 := by
    rw [abs_of_pos hR]
    exact sphere_subset_ball hR1
  have han : ∀ i, AnalyticOnNhd ℂ (g i) (disk 1) := fun i => (hg i).1.analyticOnNhd isOpen_ball
  have hm : ∀ i, MeromorphicOn (g i) (sphere (0 : ℂ) |R|) := fun i => (han i |>.mono hsub).meromorphicOn
  have hN := normalizedWronskian_analyticOnNhd han (fun i => (hg i).2)
  have hNm := (hN.mono hsub).meromorphicOn
  have hNi := hNm.inv.circleIntegrable_posLog_norm
  have he := wronskianBoundaryError_circleIntegrable (B := B) hm
  obtain ⟨w,hw,hnw⟩ := hW
  have hWe := holomorphic_nonzero_codiscrete_circle (wronskian_analyticOnNhd han).differentiableOn
    hR.le hR1 hw hnw
  have hpoint : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|),
      Real.posLog ‖g j z‖ ≤ Real.posLog ‖(normalizedWronskian g z)⁻¹‖ + wronskianBoundaryError g B z := by
    filter_upwards [hWe,self_mem_codiscreteWithin (sphere (0 : ℂ) |R|)] with z hnz hz
    have hzR : z ∈ sphere (0 : ℂ) R := by simpa only [abs_of_pos hR] using hz
    exact unit_posLog_le_normalizedWronskian_inv hB (fun i => han i z (hsub hz))
      (fun i => (hg i).2 z (hsub hz)) (fun k => hsum k z hzR) hnz j
  have havg := circleAverage_mono_codiscrete hR.ne' (hm j).circleIntegrable_posLog_norm
    (hNi.add he) hpoint
  rw [Real.circleAverage_add hNi he] at havg
  simpa only [proximityMean,ValueDistribution.proximity_top,Pi.inv_def] using havg

/-- The constant-sum instance used in the final Cartan branch. -/
theorem constant_sum_proximity_le_normalizedWronskian_inv {m : ℕ} {g : Fin m → ℂ → ℂ}
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hg : ∀ i, IsHolomorphicUnit (g i) (disk 1))
    (hsum : ∀ z ∈ disk 1, ∑ i, g i z = -1)
    (hW : ∃ z ∈ disk 1, wronskian g z ≠ 0) (j : Fin m) :
    proximityMean (g j) R ≤ proximityMean (fun z => (normalizedWronskian g z)⁻¹) R +
      Real.circleAverage (wronskianBoundaryError g 0) 0 R := by
  apply unit_proximity_le_normalizedWronskian_inv hR hR1 (by norm_num) hg hW _ j
  intro k z hz
  have hzD : z ∈ disk 1 := sphere_subset_ball hR1 hz
  have he : (fun w => ∑ i, g i w) =ᶠ[𝓝 z] (fun _ => (-1 : ℂ)) := by
    filter_upwards [isOpen_ball.mem_nhds hzD] with w hw
    exact hsum w hw
  rw [Filter.EventuallyEq.iteratedDeriv_eq (k : ℕ) he,iteratedDeriv_const]
  split_ifs <;> norm_num

end ModifiedCartan
