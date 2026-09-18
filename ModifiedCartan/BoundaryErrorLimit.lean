import ModifiedCartan.WronskianMean
import ModifiedCartan.NegligibleDerivatives

noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics Metric Set
namespace ModifiedCartan

theorem wronskian_boundary_error_negligible {m : ℕ} {η ell : ℝ}
    (hη : 0 < η) (hηh : η < 1 / 2) (hell : 0 < ell)
    (a : Fin m → ℕ → ℂ → ℂ) (r R M : ℕ → ℝ) (B : ℝ)
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hr : ∀ n, 0 ≤ r n ∧ r n < 1) (hM : Tendsto M atTop atTop)
    (hevent : ∀ᶠ n in atTop, 1 / 2 ≤ r n ∧ r n < R n ∧ R n < 1 ∧
      R n - r n = 1 / M n ∧ ∀ i,
        ell ≤ diskSupNorm (a i n) η ∧ proximityMean (a i n) (R n) ≤ 2 * M n) :
    (fun n => Real.circleAverage (wronskianBoundaryError (fun i => a i n) B) 0 (r n)) =o[atTop] M := by
  have hi : ∀ i (k : Fin m),
      (fun n => proximityMean (fun z => iteratedDeriv (k : ℕ) (a i n) z / a i n z) (r n)) =o[atTop] M := by
    intro i k
    apply derivative_quotient_growth_negligible hη hηh hell k (a i) r R M (ha i) hM
    filter_upwards [hevent] with n hn
    exact ⟨(hn.2.2.2.2 i).1, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, (hn.2.2.2.2 i).2⟩
  have hsum := IsLittleO.sum (s := Finset.univ) (fun i _ =>
    IsLittleO.sum (s := Finset.univ) (fun k _ => hi i k))
  have hconst := (isLittleO_const_id_atTop (Real.log (m.factorial : ℝ) + B)).comp_tendsto hM
  apply (hconst.add hsum).congr_left
  intro n
  have hsub : sphere (0 : ℂ) |r n| ⊆ disk 1 := by
    rw [abs_of_nonneg (hr n).1]
    exact sphere_subset_ball (hr n).2
  have hh := wronskianBoundaryError_circleAverage
    (B := B) (fun i => ((ha i n).analyticOnNhd isOpen_ball |>.mono hsub).meromorphicOn)
  simpa only [Function.comp_def, Finset.sum_apply] using hh.symm

end ModifiedCartan
