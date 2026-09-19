import ModifiedCartan.WronskianCommonFactor
import ModifiedCartan.WronskianQuotients
import ModifiedCartan.InteriorDerivativeGrowth
import ModifiedCartan.QuotientGrowth

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

theorem normalizedWronskian_proximity_quotients_bound {m : ℕ}
    {g : Fin m → ℂ → ℂ} {h : ℂ → ℂ} {r : ℝ}
    (hg : ∀ j, IsHolomorphicUnit (g j) (disk 1))
    (hh : IsHolomorphicUnit h (disk 1)) (hr : 0 ≤ r) (hr1 : r < 1) :
    proximityMean (normalizedWronskian g) r ≤ Real.log (m.factorial : ℝ) +
      ∑ j, ∑ k : Fin m, proximityMean
        (fun z => iteratedDeriv (k : ℕ) (fun w => g j w / h w) z / (g j z / h z)) r := by
  have hsub : sphere (0 : ℂ) |r| ⊆ disk 1 := by
    rw [abs_of_nonneg hr]
    exact sphere_subset_ball hr1
  have he : EqOn (normalizedWronskian (fun j z => g j z/h z))
      (normalizedWronskian g) (sphere (0 : ℂ) |r|) := by
    intro z hz
    exact normalizedWronskian_common_divisor
      (fun j => (hg j).1.analyticOnNhd isOpen_ball z (hsub hz))
      (hh.1.analyticOnNhd isOpen_ball z (hsub hz)) (hh.2 z (hsub hz))
  rw [← proximityMean_congr_circle he]
  exact normalizedWronskian_proximity_bound
    (fun j => ((unit_quotient (hg j) hh).1.analyticOnNhd isOpen_ball |>.mono hsub).meromorphicOn)

/-- After any common unit normalization, normalized Wronskians have the
same logarithmic growth bound as the derivative quotients of the normalized
functions. No nonzero Wronskian hypothesis is needed for this upper bound. -/
theorem normalizedWronskian_growth_bound {η τ r₀ : ℝ}
    (hη : 0 < η) (hηr : η < r₀) (hτ : 0 < τ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (g : Fin m → ℂ → ℂ) (h : ℂ → ℂ) (r R M : ℝ),
      (∀ j, IsHolomorphicUnit (g j) (disk 1)) → IsHolomorphicUnit h (disk 1) →
      (∀ j, τ ≤ diskSupNorm (fun z => g j z/h z) η) →
      r₀ ≤ r → r < R → R < 1 → 1 ≤ M → R-r = 1/M →
      (∀ j, proximityMean (fun z => g j z/h z) R ≤ 2*M) →
      proximityMean (normalizedWronskian g) r ≤ B*(Real.log M+1) := by
  classical
  have hb := fun k : Fin m => interior_derivative_quotient_growth_bound hη hηr hτ (k : ℕ)
  choose B hB hbound using hb
  have hfac : 0 ≤ Real.log (m.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos m)))
  refine ⟨Real.log (m.factorial : ℝ) + (m : ℝ)*∑ k, B k,
    add_nonneg hfac (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun k _ => hB k))), ?_⟩
  intro g h r R M hg hh ha hr hrR hR hM hgap hm
  have hL : 1 ≤ Real.log M+1 := by linarith [Real.log_nonneg hM]
  have hsum : (∑ j : Fin m, ∑ k : Fin m, proximityMean
      (fun z => iteratedDeriv (k : ℕ) (fun w => g j w/h w) z/(g j z/h z)) r) ≤
      (m : ℝ)*(∑ k, B k)*(Real.log M+1) := by
    calc
      _ ≤ ∑ _j : Fin m, ∑ k : Fin m, B k*(Real.log M+1) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hbound k (fun z => g j z/h z) r R M (unit_quotient (hg j) hh).1
          (ha j) hr hrR hR hM hgap (hm j)
      _ = _ := by simp [← Finset.sum_mul, mul_assoc]
  have hbase := normalizedWronskian_proximity_quotients_bound hg hh
    (hη.le.trans (hηr.le.trans hr)) (hrR.trans hR)
  have hc := mul_le_mul_of_nonneg_left hL hfac
  nlinarith

end ModifiedCartan
