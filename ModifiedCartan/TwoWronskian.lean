import ModifiedCartan.WronskianMean
import ModifiedCartan.PoissonMajorant

noncomputable section
set_option autoImplicit false
open Filter Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

theorem wronskian_two (a : Fin 2 → ℂ → ℂ) (z : ℂ) :
    wronskian a z = a 0 z * deriv (a 1) z - a 1 z * deriv (a 0) z := by
  simp [wronskian, Matrix.det_fin_two, iteratedDeriv_zero, iteratedDeriv_one]

theorem deriv_two_term_quotient {a : Fin 2 → ℂ → ℂ} {z : ℂ}
    (ha : ∀ i, DifferentiableAt ℂ (a i) z) (hs : a 0 z + a 1 z ≠ 0) :
    deriv (fun w => a 0 w / (a 0 w + a 1 w)) z =
      -wronskian a z / (a 0 z + a 1 z) ^ 2 := by
  have hd := ((ha 0).hasDerivAt.div ((ha 0).hasDerivAt.add (ha 1).hasDerivAt) hs).deriv
  simp only [Pi.div_def, Pi.add_def] at hd
  rw [hd, wronskian_two]
  congr 1
  ring

/-- The actual two-column Wronskian is controlled by the lower harmonic
envelope and the actual integrated derivative error. -/
theorem two_wronskian_poisson_majorant {a A : Fin 2 → ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hR1 : R < 1) (hB : 0 ≤ B)
    (ha : ∀ i, DifferentiableOn ℂ (a i) (disk 1))
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1))
    (han : ∀ i, ∃ z ∈ disk 1, a i z ≠ 0)
    (hdom : ∀ i z, z ∈ sphere (0 : ℂ) R → ‖a i z‖ ≤ ‖A i z‖)
    (hsum : ∀ (k : Fin 2) z, z ∈ sphere (0 : ℂ) R →
      ‖iteratedDeriv (k : ℕ) (fun w => ∑ i, a i w) z‖ ≤ Real.exp B)
    (hpos : ∀ z ∈ sphere (0 : ℂ) R, ∃ i, 1 < ‖A i z‖)
    {w : ℂ} (hw : w ∈ disk R) :
    ‖wronskian a w‖ ≤ Real.exp
      (Real.log ‖A 0 w‖ + Real.log ‖A 1 w‖ -
        poissonExtension (fun z => maxWithZero (fun i => Real.log ‖A i z‖)) R w +
        (R + ‖w‖) / (R - ‖w‖) * Real.circleAverage (wronskianBoundaryError a B) 0 R) := by
  let u := fun i z => Real.log ‖A i z‖
  let v := fun z => maxWithZero (fun i => u i z)
  let S := fun z => u 0 z + u 1 z
  have hsub : sphere (0 : ℂ) |R| ⊆ disk 1 := by
    rw [abs_of_pos hR]
    exact sphere_subset_ball hR1
  have hui : ∀ i, CircleIntegrable (u i) 0 R := fun i =>
    ((unit_log_harmonic (hA i)).continuousOn.mono hsub).circleIntegrable'
  have hv : CircleIntegrable v 0 R :=
    ((continuousOn_maxWithZero (fun i => (unit_log_harmonic (hA i)).continuousOn)).mono hsub).circleIntegrable'
  have hS : CircleIntegrable S 0 R := by simpa only [Pi.add_def] using (hui 0).add (hui 1)
  have hamer : ∀ i, MeromorphicOn (a i) (sphere (0 : ℂ) |R|) :=
    fun i => ((ha i).analyticOnNhd isOpen_ball |>.mono hsub).meromorphicOn
  have he := wronskianBoundaryError_circleIntegrable (B := B) hamer
  have hWholo := wronskian_analyticOnNhd (fun i => (ha i).analyticOnNhd isOpen_ball)
  have hanz : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|), ∀ i, a i z ≠ 0 := by
    apply eventually_all.mpr
    intro i
    obtain ⟨z, hz, hnz⟩ := han i
    exact holomorphic_nonzero_codiscrete_circle (ha i) hR.le hR1 hz hnz
  have hbound : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|),
      wronskian a z ≠ 0 → Real.log ‖wronskian a z‖ ≤ (S z - v z) + wronskianBoundaryError a B z := by
    filter_upwards [hanz, self_mem_codiscreteWithin (sphere (0 : ℂ) |R|)] with z hanz hz
    intro hW
    have hzR : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hz
    have h := (wronskian_boundary_max_estimates (by norm_num : 1 ≤ 2) hB
      (fun i => (ha i).analyticOnNhd isOpen_ball z (hsub hz)) hanz
      (fun i => (hA i).2 z (hsub hz)) (fun i => hdom i z hzR)
      (fun k => hsum k z hzR) hW (hpos z hzR)).1
    simpa only [Fin.sum_univ_two] using h
  have h := norm_le_exp_poisson_majorant (hWholo.mono (closedBall_subset_ball hR1))
    (by simpa only [Pi.sub_def] using hS.sub hv) he
    (fun z _ => wronskianBoundaryError_nonneg a hB z) hbound hw
  have hSharm : HarmonicContOnCl S (ball (0 : ℂ) R) := by
    apply HarmonicOnNhd.harmonicContOnCl
    rw [closure_ball _ hR.ne']
    exact ((unit_log_harmonic (hA 0)).add (unit_log_harmonic (hA 1))).mono
      (closedBall_subset_ball hR1)
  rw [poissonExtension_sub hS hv hw, poissonExtension_eq_harmonic hSharm hw] at h
  exact h

end ModifiedCartan
