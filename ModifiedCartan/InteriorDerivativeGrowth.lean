import ModifiedCartan.NegligibleDerivatives
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics Real
namespace ModifiedCartan

/-- The original logarithmic-derivative estimate on a growth-controlled circle
has a uniform O(log M) bound with no nonvanishing assumption on the functions. -/
theorem interior_derivative_quotient_growth_bound {η τ r₀ : ℝ} (hη : 0 < η) (hηh : η < r₀)
    (hτ : 0 < τ) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (f : ℂ → ℂ) (r R M : ℝ),
      DifferentiableOn ℂ f (disk 1) → τ ≤ diskSupNorm f η →
      r₀ ≤ r → r < R → R < 1 → 1 ≤ M → R - r = 1 / M →
      proximityMean f R ≤ 2 * M →
      proximityMean (fun z => iteratedDeriv k f z / f z) r ≤ B * (Real.log M + 1) := by
  obtain ⟨C, hC, hest⟩ := higher_derivative_quotient_mean hη hηh k
  let D := 4 + Real.posLog (1 / τ)
  have hp : 0 ≤ Real.posLog (1 / τ) := Real.posLog_nonneg
  have hD : 0 < D := by dsimp [D]; linarith
  have hD1 : 1 ≤ D := by dsimp [D]; linarith [Real.posLog_nonneg (x := 1 / τ)]
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  refine ⟨C * (Real.log D + 2), mul_nonneg hC (by linarith), ?_⟩
  intro f r R M hf hτf hr hrR hR hM hgap hmean
  have hM0 : 0 < M := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hbase := hest f τ r R hf hτ hτf hr hrR hR
  have hpoly : 2 + proximityMean f R + Real.posLog (1 / τ) ≤ D * M := by
    dsimp [D]
    nlinarith [mul_nonneg (Real.posLog_nonneg (x := 1 / τ)) (sub_nonneg.mpr hM)]
  have hmean0 : 0 ≤ proximityMean f R := ValueDistribution.proximity_nonneg _
  have hlog := Real.log_le_log (by linarith : 0 < 2 + proximityMean f R + Real.posLog (1 / τ)) hpoly
  rw [Real.log_mul hD.ne' hM0.ne'] at hlog
  rw [hgap, one_div_one_div] at hbase
  apply hbase.trans
  have hmul := mul_le_mul_of_nonneg_left hlog hC
  nlinarith [mul_nonneg hlogD hlogM, mul_nonneg hC (mul_nonneg hlogD hlogM)]

theorem interior_derivative_quotient_growth_negligible {η τ r₀ : ℝ} (hη : 0 < η) (hηh : η < r₀)
    (hτ : 0 < τ) (k : ℕ) (f : ℕ → ℂ → ℂ) (r R M : ℕ → ℝ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (disk 1)) (hM : Tendsto M atTop atTop)
    (hevent : ∀ᶠ n in atTop, τ ≤ diskSupNorm (f n) η ∧
      r₀ ≤ r n ∧ r n < R n ∧ R n < 1 ∧ R n - r n = 1 / M n ∧
      proximityMean (f n) (R n) ≤ 2 * M n) :
    (fun n => proximityMean (fun z => iteratedDeriv k (f n) z / f n z) (r n)) =o[atTop] M := by
  obtain ⟨B, hB, hbound⟩ := interior_derivative_quotient_growth_bound hη hηh hτ k
  apply (IsBigO.of_bound' ?_).trans_isLittleO (log_growth_error_isLittleO hM B)
  filter_upwards [hevent, hM.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hMn
  have hp : 0 ≤ proximityMean (fun z => iteratedDeriv k (f n) z / f n z) (r n) :=
    ValueDistribution.proximity_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hp,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB (by linarith [Real.log_nonneg hMn]))]
  exact hbound (f n) (r n) (R n) (M n) (hf n) hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1
    hMn hn.2.2.2.2.1 hn.2.2.2.2.2

end ModifiedCartan
