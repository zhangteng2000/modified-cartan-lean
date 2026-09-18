import ModifiedCartan.SharpTwoSetup
import ModifiedCartan.UnitEnvelope
import ModifiedCartan.InteriorBoundaryError
import ModifiedCartan.TwoWronskian
import ModifiedCartan.ConvergenceJets
import ModifiedCartan.AbsorptionEnvelope

noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics Metric Set
namespace ModifiedCartan

theorem sharp_two_analytic_bounds {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ} {Ω : Set ℂ}
    (D : SharpTwoSetup A a s Ω)
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk 1))
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1)) :
    ∃ B : ℝ, 0 ≤ B ∧
      (fun n => Real.circleAverage (wronskianBoundaryError (fun i => a i n) B) 0 (D.ρ n))
        =o[atTop] (fun n => unitGrowthMean (fun i => A i n) (D.ρ n)) ∧
      ∀ᶠ n in atTop, ∀ w ∈ disk (D.ρ n),
        ‖wronskian (fun i => a i n) w‖ ≤ Real.exp
          (Real.log ‖A 0 n w‖ + Real.log ‖A 1 n w‖ - unitEnvelope (fun i => A i n) (D.ρ n) w +
            (D.ρ n + ‖w‖) / (D.ρ n - ‖w‖) *
              Real.circleAverage (wronskianBoundaryError (fun i => a i n) B) 0 (D.ρ n)) := by
  let M := fun n => unitGrowthMean (fun i => A i n) (D.ρ n)
  let R := fun n => D.ρ n + 1 / M n
  have hα : 0 < D.α := D.r_pos.trans D.r_lt
  have hβ1 : D.β < 1 := D.β_lt.trans D.v_lt
  have hα1 : D.α < 1 := D.α_lt.trans hβ1
  have hr1 : D.r < 1 := D.r_lt.trans hα1
  have hρ0 : ∀ n, 0 < D.ρ n := fun n => hα.trans_le (D.radius n).1
  have hρ1 : ∀ n, D.ρ n < 1 := fun n => (D.radius n).2.trans hβ1
  obtain ⟨B, hB, hjet⟩ := compactConvergence_jet_bound isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
    (closedBall_subset_ball D.v_lt) (isCompact_closedBall (0 : ℂ) D.v) 2
  have hdata : ∀ᶠ n in atTop, D.α ≤ D.ρ n ∧ D.ρ n < R n ∧ R n < 1 ∧
      R n - D.ρ n = 1 / M n ∧ ∀ i,
        D.ell ≤ diskSupNorm (a i n) D.r ∧ proximityMean (a i n) (R n) ≤ 2 * M n := by
    filter_upwards [D.controlled, D.interior_norms] with n hn hnorm
    have hMn : 0 < M n := hn.1
    have hρR : D.ρ n < R n := lt_add_of_pos_right _ (one_div_pos.mpr hMn)
    have hRβ : R n < D.β := hn.2.1
    have hR1 : R n < 1 := hRβ.trans hβ1
    refine ⟨(D.radius n).1, hρR, hR1, by dsimp [R]; ring, ?_⟩
    intro i
    refine ⟨hnorm i, le_trans ?_ hn.2.2.1⟩
    apply proximityMean_le_unitGrowthMean ((hρ0 n).trans hρR).le hR1 (fun i => hA i n)
      (((ha i n).analyticOnNhd isOpen_ball).mono (sphere_subset_ball hR1) |>.meromorphicOn) i
    intro z hz
    have hzn : ‖z‖ = R n := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hn.2.2.2.2 i z (by rw [hzn]; exact (hRβ.trans D.β_lt).le)
  have herr := interior_wronskian_boundary_error_negligible D.r_pos D.r_lt D.ell_pos
    a D.ρ R M B ha (fun n => ⟨(hρ0 n).le, hρ1 n⟩) D.growth hdata
  refine ⟨B, hB, herr, ?_⟩
  filter_upwards [D.controlled, D.interior_norms] with n hn hnorm w hw
  apply two_wronskian_poisson_majorant (hρ0 n) (hρ1 n) hB
    (fun i => ha i n) (fun i => hA i n) ?_ ?_ ?_ hn.2.2.2.1 hw
  · intro i
    obtain ⟨z, hz, he⟩ := diskSupNorm_attained D.r_pos.le
      ((ha i n).continuousOn.mono (closedBall_subset_ball hr1))
    refine ⟨z, closedBall_subset_ball hr1 hz, norm_pos_iff.mp ?_⟩
    rw [← he]
    exact D.ell_pos.trans_le (hnorm i)
  · intro i z hz
    have hzn : ‖z‖ = D.ρ n := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hn.2.2.2.2 i z (by rw [hzn]; exact ((D.radius n).2.trans D.β_lt).le)
  · intro k z hz
    apply hjet n k z
    exact sphere_subset_closedBall.trans (closedBall_subset_closedBall
      ((D.radius n).2.trans D.β_lt).le) hz

end ModifiedCartan
