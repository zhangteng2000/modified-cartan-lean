import ModifiedCartan.WronskianBoundary
import ModifiedCartan.UnitGrowth
import ModifiedCartan.DerivativeQuotientRecurrence

noncomputable section
set_option autoImplicit false
open Filter Metric Real Set InnerProductSpace
namespace ModifiedCartan

def wronskianBoundaryError {m : ℕ} (a : Fin m → ℂ → ℂ) (B : ℝ) (z : ℂ) : ℝ :=
  Real.log (m.factorial : ℝ) + B + ∑ i, derivativeColumnError (m := m) (a i) z

theorem wronskianBoundaryError_nonneg {m : ℕ} (a : Fin m → ℂ → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (z : ℂ) : 0 ≤ wronskianBoundaryError a B z := by
  have hf : 0 ≤ Real.log (m.factorial : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos m)
  exact add_nonneg (add_nonneg hf hB)
    (Finset.sum_nonneg (fun i _ => derivativeColumnError_nonneg (a i) z))

theorem wronskianBoundaryError_circleIntegrable {m : ℕ} {a : Fin m → ℂ → ℂ} {R B : ℝ}
    (ha : ∀ i, MeromorphicOn (a i) (sphere (0 : ℂ) |R|)) :
    CircleIntegrable (wronskianBoundaryError a B) 0 R := by
  have hi := fun (i k : Fin m) =>
    ((meromorphicOn_iteratedDeriv (ha i) k).div (ha i)).circleIntegrable_posLog_norm
  convert
    (circleIntegrable_const (Real.log (m.factorial : ℝ) + B) 0 R).add
      (CircleIntegrable.sum Finset.univ (fun i _ => CircleIntegrable.sum Finset.univ (fun k _ => hi i k))) using 1
  ext z
  simp only [wronskianBoundaryError, derivativeColumnError, Pi.add_apply, Finset.sum_apply, Pi.div_apply]

theorem wronskianBoundaryError_circleAverage {m : ℕ} {a : Fin m → ℂ → ℂ} {R B : ℝ}
    (ha : ∀ i, MeromorphicOn (a i) (sphere (0 : ℂ) |R|)) :
    Real.circleAverage (wronskianBoundaryError a B) 0 R =
      Real.log (m.factorial : ℝ) + B +
        ∑ i, ∑ k : Fin m, proximityMean (fun z => iteratedDeriv (k : ℕ) (a i) z / a i z) R := by
  have hi : ∀ i (k : Fin m), CircleIntegrable
      (fun z => Real.posLog ‖iteratedDeriv (k : ℕ) (a i) z / a i z‖) 0 R :=
    fun i k => ((meromorphicOn_iteratedDeriv (ha i) k).div (ha i)).circleIntegrable_posLog_norm
  have he : wronskianBoundaryError a B = ((fun _ : ℂ => Real.log (m.factorial : ℝ) + B) +
    ∑ i : Fin m, ∑ k : Fin m, fun z => Real.posLog ‖iteratedDeriv (k : ℕ) (a i) z / a i z‖) := by
    ext z
    simp only [wronskianBoundaryError, derivativeColumnError, Pi.add_apply, Finset.sum_apply]
  rw [he]
  rw [Real.circleAverage_add (circleIntegrable_const _ _ _)
    (CircleIntegrable.sum _ (fun i _ => CircleIntegrable.sum _ (fun k _ => hi i k))),
    Real.circleAverage_const, Real.circleAverage_sum (fun i _ => CircleIntegrable.sum _ (fun k _ => hi i k))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.circleAverage_sum (fun k _ => hi i k)]
  rfl

theorem exists_maxWithZero_eq {m : ℕ} (u : Fin m → ℝ) (hpos : ∃ i, 0 < u i) :
    ∃ j, maxWithZero u = u j := by
  classical
  obtain ⟨i, hi⟩ := hpos
  let : Nonempty (Fin m) := ⟨i⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  refine ⟨j, le_antisymm ?_ (le_maxWithZero u j)⟩
  exact maxWithZero_le (hi.le.trans (hmax i (Finset.mem_univ i)))
    (fun k => hmax k (Finset.mem_univ k))

theorem wronskian_boundary_max_estimates {m : ℕ} (hm : 1 ≤ m)
    {a : Fin m → ℂ → ℂ} {A : Fin m → ℂ} {z : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ i, AnalyticAt ℂ (a i) z) (han : ∀ i, a i z ≠ 0) (hAn : ∀ i, A i ≠ 0)
    (hdom : ∀ i, ‖a i z‖ ≤ ‖A i‖)
    (hsum : ∀ k : Fin m, ‖iteratedDeriv (k : ℕ) (fun w => ∑ i, a i w) z‖ ≤ Real.exp B)
    (hW : wronskian a z ≠ 0) (hpos : ∃ i, 1 < ‖A i‖) :
    Real.log ‖wronskian a z‖ ≤ (∑ i, Real.log ‖A i‖) - maxWithZero (fun i => Real.log ‖A i‖) +
      wronskianBoundaryError a B z ∧
    Real.posLog ‖wronskian a z‖ ≤ ((m : ℝ) - 1) * maxWithZero (fun i => Real.log ‖A i‖) +
      wronskianBoundaryError a B z := by
  let v := maxWithZero (fun i => Real.log ‖A i‖)
  obtain ⟨j, hj⟩ := exists_maxWithZero_eq (fun i => Real.log ‖A i‖)
    (hpos.imp (fun i hi => Real.log_pos hi))
  have hlog := wronskian_boundary_log_bound ha han hAn hdom hsum hW j
  rw [← hj] at hlog
  refine ⟨hlog, ?_⟩
  have hsumlog : (∑ i, Real.log ‖A i‖) ≤ (m : ℝ) * v := by
    calc
      _ ≤ ∑ _i : Fin m, v := Finset.sum_le_sum (fun i _ => le_maxWithZero (fun i => Real.log ‖A i‖) i)
      _ = _ := by simp
  rw [Real.posLog_apply]
  apply max_le
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hm)) (maxWithZero_nonneg _))
      (wronskianBoundaryError_nonneg a hB z)
  · change Real.log ‖wronskian a z‖ ≤ ((m : ℝ) - 1) * v + _
    change Real.log ‖wronskian a z‖ ≤ (∑ i, Real.log ‖A i‖) - v + _ at hlog
    unfold wronskianBoundaryError
    linarith

/-- Both integrated boundary estimates, with all zeros allowed on the circle. -/
theorem wronskian_boundary_mean_estimates {m : ℕ} (hm : 1 ≤ m)
    {a A : Fin m → ℂ → ℂ} {R B : ℝ} (hR : 0 < R) (hR1 : R < 1) (hB : 0 ≤ B)
    (ha : ∀ i, DifferentiableOn ℂ (a i) (disk 1))
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1))
    (han : ∀ i, ∃ z ∈ disk 1, a i z ≠ 0)
    (hW : ∃ z ∈ disk 1, wronskian a z ≠ 0)
    (hdom : ∀ i z, z ∈ sphere (0 : ℂ) R → ‖a i z‖ ≤ ‖A i z‖)
    (hsum : ∀ (k : Fin m) z, z ∈ sphere (0 : ℂ) R →
      ‖iteratedDeriv (k : ℕ) (fun w => ∑ i, a i w) z‖ ≤ Real.exp B)
    (hpos : ∀ z ∈ sphere (0 : ℂ) R, ∃ i, 1 < ‖A i z‖) :
    let E := Real.circleAverage (wronskianBoundaryError a B) 0 R
    Real.circleAverage (fun z => Real.log ‖wronskian a z‖) 0 R ≤
      (∑ i, Real.log ‖A i 0‖) - unitGrowthMean A R + E ∧
    proximityMean (wronskian a) R ≤ ((m : ℝ) - 1) * unitGrowthMean A R + E := by
  let u := fun i z => Real.log ‖A i z‖
  let v := fun z => maxWithZero (fun i => u i z)
  let S := fun z => ∑ i, u i z
  let e := wronskianBoundaryError a B
  have hsub : sphere (0 : ℂ) |R| ⊆ disk 1 := by
    rw [abs_of_pos hR]
    exact sphere_subset_ball hR1
  have hamer : ∀ i, MeromorphicOn (a i) (sphere (0 : ℂ) |R|) :=
    fun i => ((ha i).analyticOnNhd isOpen_ball |>.mono hsub).meromorphicOn
  have hWholo := wronskian_analyticOnNhd (fun i => (ha i).analyticOnNhd isOpen_ball)
  have hWmer := (hWholo.mono hsub).meromorphicOn
  have hui : ∀ i, CircleIntegrable (u i) 0 R :=
    fun i => ((unit_log_harmonic (hA i)).continuousOn.mono hsub).circleIntegrable'
  have hv : CircleIntegrable v 0 R :=
    ((continuousOn_maxWithZero (fun i => (unit_log_harmonic (hA i)).continuousOn)).mono hsub).circleIntegrable'
  have hS : CircleIntegrable S 0 R := by
    convert CircleIntegrable.sum Finset.univ (fun i _ => hui i) using 1
    ext z
    simp only [S, Finset.sum_apply]
  have he : CircleIntegrable e 0 R := wronskianBoundaryError_circleIntegrable hamer
  have hame : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|), ∀ i, a i z ≠ 0 := by
    apply eventually_all.mpr
    intro i
    obtain ⟨z, hz, hnz⟩ := han i
    exact holomorphic_nonzero_codiscrete_circle (ha i) hR.le hR1 hz hnz
  obtain ⟨w, hw, hnw⟩ := hW
  have hWme := holomorphic_nonzero_codiscrete_circle hWholo.differentiableOn hR.le hR1 hw hnw
  have hpoint : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|),
      Real.log ‖wronskian a z‖ ≤ S z - v z + e z ∧
      Real.posLog ‖wronskian a z‖ ≤ ((m : ℝ) - 1) * v z + e z := by
    filter_upwards [hame, hWme, self_mem_codiscreteWithin (sphere (0 : ℂ) |R|)] with z hanz hWz hz
    have hzR : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hz
    exact wronskian_boundary_max_estimates hm hB
      (fun i => (ha i).analyticOnNhd isOpen_ball z (hsub hz)) hanz
      (fun i => (hA i).2 z (hsub hz)) (fun i => hdom i z hzR)
      (fun k => hsum k z hzR) hWz (hpos z hzR)
  have havgS : Real.circleAverage S 0 R = ∑ i, u i 0 := by
    have he : S = ∑ i : Fin m, u i := by ext z; simp [S]
    rw [he]
    rw [Real.circleAverage_sum (fun i _ => hui i)]
    apply Finset.sum_congr rfl
    intro i _
    exact InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      ((unit_log_harmonic (hA i)).mono (by
        rw [abs_of_pos hR]
        exact closedBall_subset_ball hR1))
  constructor
  · have hi : CircleIntegrable (fun z => S z - v z + e z) 0 R := by
      simpa only [Pi.add_def, Pi.sub_def] using (hS.sub hv).add he
    have hh := circleAverage_mono_codiscrete hR.ne' hWmer.circleIntegrable_log_norm hi
      (hpoint.mono (fun z hz => hz.1))
    have havg : Real.circleAverage (fun z => S z - v z + e z) 0 R =
        Real.circleAverage S 0 R - Real.circleAverage v 0 R + Real.circleAverage e 0 R := by
      change Real.circleAverage ((S - v) + e) 0 R = _
      rw [Real.circleAverage_add (hS.sub hv) he, Real.circleAverage_sub hS hv]
    rw [havg, havgS] at hh
    exact hh
  · have hi : CircleIntegrable (fun z => ((m : ℝ) - 1) * v z + e z) 0 R := by
      simpa only [Pi.add_def, Pi.smul_def, smul_eq_mul] using (hv.const_smul (a := (m : ℝ) - 1)).add he
    have hh := circleAverage_mono_codiscrete hR.ne' hWmer.circleIntegrable_posLog_norm hi
      (hpoint.mono (fun z hz => hz.2))
    have havg : Real.circleAverage (fun z => ((m : ℝ) - 1) * v z + e z) 0 R =
        ((m : ℝ) - 1) * Real.circleAverage v 0 R + Real.circleAverage e 0 R := by
      change Real.circleAverage (((m : ℝ) - 1) • v + e) 0 R = _
      rw [Real.circleAverage_add (hv.const_smul (a := (m : ℝ) - 1)) he, Real.circleAverage_smul]
      rfl
    rw [havg] at hh
    exact hh

end ModifiedCartan
