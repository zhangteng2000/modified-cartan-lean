import ModifiedCartan.WronskianMean
import ModifiedCartan.WronskianFourIdentity

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

def normalizedWronskian {m : ℕ} (g : Fin m → ℂ → ℂ) (z : ℂ) : ℂ :=
  wronskian g z / ∏ j, g j z

theorem normalizedWronskian_eq_det {m : ℕ} (g : Fin m → ℂ → ℂ) (z : ℂ) :
    normalizedWronskian g z =
      Matrix.det (.of fun k j : Fin m => iteratedDeriv (k : ℕ) (g j) z / g j z) := by
  simpa [normalizedWronskian,wronskian,div_eq_mul_inv,Finset.prod_inv_distrib,mul_comm] using
    (Matrix.det_mul_row (fun j => (g j z)⁻¹)
      (.of fun k j : Fin m => iteratedDeriv (k : ℕ) (g j) z)).symm

theorem normalizedWronskian_analyticOnNhd {m : ℕ} {g : Fin m → ℂ → ℂ} {U : Set ℂ}
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) (hnz : ∀ j z, z ∈ U → g j z ≠ 0) :
    AnalyticOnNhd ℂ (normalizedWronskian g) U := by
  intro z hz
  exact (wronskian_analyticOnNhd hg z hz).div
    (Finset.analyticAt_fun_prod Finset.univ (fun j _ => hg j z hz))
    (Finset.prod_ne_zero_iff.mpr (fun j _ => hnz j z hz))

theorem normalizedWronskian_two {f g : ℂ → ℂ} {z : ℂ} (hf : f z ≠ 0) (hg : g z ≠ 0) :
    normalizedWronskian ![f,g] z = logDeriv g z - logDeriv f z := by
  simp [normalizedWronskian,wronskian_two,Fin.prod_univ_two,logDeriv]
  field_simp

theorem normalizedWronskian_three_factor {g : Fin 3 → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, g j z ≠ 0) (h01 : wronskian ![g 0,g 1] z ≠ 0)
    (h02 : wronskian ![g 0,g 2] z ≠ 0) :
    normalizedWronskian g z /
      (normalizedWronskian ![g 0,g 1] z * normalizedWronskian ![g 0,g 2] z) =
      g 0 z * wronskian g z / (wronskian ![g 0,g 1] z * wronskian ![g 0,g 2] z) := by
  simp only [normalizedWronskian,Fin.prod_univ_three,Fin.prod_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [hg 0,hg 1,hg 2]
  <;> ring

theorem normalizedWronskian_posLog_bound {m : ℕ} (g : Fin m → ℂ → ℂ) (z : ℂ) :
    Real.posLog ‖normalizedWronskian g z‖ ≤ wronskianBoundaryError g 0 z := by
  have hentry : ∀ k j : Fin m, ‖iteratedDeriv (k : ℕ) (g j) z / g j z‖ ≤
      Real.exp (derivativeColumnError (m := m) (g j) z) := by
    intro k j
    have hb : Real.posLog ‖iteratedDeriv (k : ℕ) (g j) z / g j z‖ ≤
        derivativeColumnError (m := m) (g j) z :=
      Finset.single_le_sum (f := fun i : Fin m => Real.posLog ‖iteratedDeriv (i : ℕ) (g j) z / g j z‖)
        (fun _ _ => Real.posLog_nonneg) (Finset.mem_univ k)
    by_cases hn : iteratedDeriv (k : ℕ) (g j) z / g j z = 0
    · simpa [hn] using (Real.exp_pos (derivativeColumnError (m := m) (g j) z)).le
    · rw [← Real.exp_log (norm_pos_iff.mpr hn)]
      exact Real.exp_le_exp.mpr ((le_max_right _ _).trans hb)
  have hd := matrix_det_norm_column_bound
    (.of fun k j : Fin m => iteratedDeriv (k : ℕ) (g j) z / g j z)
    (fun j => Real.exp (derivativeColumnError (m := m) (g j) z))
    (fun j => (Real.exp_pos _).le) hentry
  rw [← normalizedWronskian_eq_det] at hd
  have he : (m.factorial : ℝ) * ∏ j, Real.exp (derivativeColumnError (m := m) (g j) z) =
      Real.exp (wronskianBoundaryError g 0 z) := by
    simp only [wronskianBoundaryError,add_zero,Real.exp_add,Real.exp_sum]
    rw [Real.exp_log (by exact_mod_cast Nat.factorial_pos m)]
  rw [he] at hd
  rw [Real.posLog_apply]
  apply max_le (wronskianBoundaryError_nonneg g (by norm_num) z)
  by_cases hn : normalizedWronskian g z = 0
  · simp only [hn,norm_zero,Real.log_zero]
    exact wronskianBoundaryError_nonneg g (by norm_num) z
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr hn)).mpr hd

/-- All normalized Wronskian growth is controlled by the same logarithmic
 derivative means that occur in the manuscript's proved derivative estimate. -/
theorem normalizedWronskian_proximity_bound {m : ℕ} {g : Fin m → ℂ → ℂ} {R : ℝ}
    (hg : ∀ j, MeromorphicOn (g j) (sphere (0 : ℂ) |R|)) :
    proximityMean (normalizedWronskian g) R ≤ Real.log (m.factorial : ℝ) +
      ∑ j, ∑ k : Fin m, proximityMean (fun z => iteratedDeriv (k : ℕ) (g j) z / g j z) R := by
  have hmero : MeromorphicOn (normalizedWronskian g) (sphere (0 : ℂ) |R|) := by
    intro z hz
    rw [show normalizedWronskian g = fun w => Matrix.det
      (.of fun k j : Fin m => iteratedDeriv (k : ℕ) (g j) w / g j w) from funext (normalizedWronskian_eq_det g)]
    simp only [Matrix.det_apply']
    apply MeromorphicAt.fun_sum
    intro σ _
    apply MeromorphicAt.mul (analyticAt_const.meromorphicAt)
    apply MeromorphicAt.fun_prod
    intro j _
    exact (meromorphicOn_iteratedDeriv (hg j) (σ j) z hz).div (hg j z hz)
  have hb := Real.circleAverage_mono hmero.circleIntegrable_posLog_norm
    (wronskianBoundaryError_circleIntegrable (B := 0) hg)
    (fun z _ => normalizedWronskian_posLog_bound g z)
  rw [wronskianBoundaryError_circleAverage hg] at hb
  simpa only [proximityMean,ValueDistribution.proximity_top,add_zero] using hb

end ModifiedCartan
