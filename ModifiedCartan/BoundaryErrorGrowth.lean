import ModifiedCartan.InteriorDerivativeGrowth
import ModifiedCartan.WronskianMean

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- The full integrated derivative error has a uniform logarithmic bound,
including the determinant factorial and every derivative order and column. -/
theorem wronskianBoundaryError_growth_bound {η τ r₀ : ℝ}
    (hη : 0 < η) (hηr : η < r₀) (hτ : 0 < τ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g : Fin m → ℂ → ℂ) (r R M : ℝ),
      (∀ j, DifferentiableOn ℂ (g j) (disk 1)) →
      (∀ j, τ ≤ diskSupNorm (g j) η) →
      r₀ ≤ r → r < R → R < 1 → 1 ≤ M → R-r = 1/M →
      (∀ j, proximityMean (g j) R ≤ 2*M) →
      Real.circleAverage (wronskianBoundaryError g 0) 0 r ≤ B*(Real.log M+1) := by
  classical
  have hb := fun k : Fin m => interior_derivative_quotient_growth_bound hη hηr hτ (k : ℕ)
  choose B hB hbound using hb
  have hfac : 0 ≤ Real.log (m.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos m)))
  refine ⟨Real.log (m.factorial : ℝ) + (m : ℝ)*∑ k, B k,
    add_nonneg hfac (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun k _ => hB k))), ?_⟩
  intro g r R M hg ha hr hrR hR hM hgap hm
  have hL : 1 ≤ Real.log M+1 := by linarith [Real.log_nonneg hM]
  have hsum : (∑ j : Fin m, ∑ k : Fin m, proximityMean
      (fun z => iteratedDeriv (k : ℕ) (g j) z/g j z) r) ≤
      (m : ℝ)*(∑ k, B k)*(Real.log M+1) := by
    calc
      _ ≤ ∑ _j : Fin m, ∑ k : Fin m, B k*(Real.log M+1) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hbound k (g j) r R M (hg j) (ha j) hr hrR hR hM hgap (hm j)
      _ = _ := by simp [← Finset.sum_mul,mul_assoc]
  have hr0 : 0 ≤ r := hη.le.trans (hηr.le.trans hr)
  have hsub : sphere (0 : ℂ) |r| ⊆ disk 1 := by
    rw [abs_of_nonneg hr0]
    exact sphere_subset_ball (hrR.trans hR)
  rw [wronskianBoundaryError_circleAverage
    (fun j => ((hg j).analyticOnNhd isOpen_ball |>.mono hsub).meromorphicOn)]
  have hc := mul_le_mul_of_nonneg_left hL hfac
  nlinarith

end ModifiedCartan
