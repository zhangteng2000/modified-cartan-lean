import ModifiedCartan.LogDerivativeConstants
import ModifiedCartan.LogarithmicGrowthAlgebra
import ModifiedCartan.ProximityLocal

noncomputable section
set_option autoImplicit false
open Filter Metric Set Real
namespace ModifiedCartan

/-- The manuscript's uniform logarithmic mean bound for every derivative of h′/h. -/
theorem iterated_log_derivative_mean {α r₀ : ℝ}
    (hα : 0 < α) (hαr : α < r₀) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℂ → ℂ) (τ r R : ℝ),
      DifferentiableOn ℂ F (disk 1) → 0 < τ → τ ≤ diskSupNorm F α →
      r₀ ≤ r → r < R → R < 1 →
      proximityMean (iteratedDeriv n (logDeriv F)) r ≤
        C * (Real.log (2 + proximityMean F R + Real.posLog (1 / τ)) + Real.log (1 / (R - r))) := by
  let p : ℝ := 1 / (2 * ((n + 1 : ℕ) : ℝ))
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by dsimp [p]; apply (div_le_one (by positivity)).mpr; norm_cast; omega
  have hjp : ((n + 1 : ℕ) : ℝ) * p < 1 := by
    have he : ((n + 1 : ℕ) : ℝ) * p = 1 / 2 := by dsimp [p]; field_simp
    rw [he]
    norm_num
  obtain ⟨C₀, hC₀, hpoles⟩ := logarithmic_mean_of_pole_bound (hα.trans hαr) hp hp1 hjp
  obtain ⟨A, B, hA, hB, hpoly⟩ := logDerivativeRegularBound_polynomial hα hαr n
  obtain ⟨C, hC, hgrowth⟩ := log_fractional_moment_growth hA hB
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n.factorial) p) hC₀) hp hp1 (n + 3)
  refine ⟨C, hC, ?_⟩
  intro F τ r R hF hτ hτF hr₀ hrR hR
  let E := 1 + 4 * proximityMean F R / (R - r) + Real.posLog (1 / τ)
  let b := 2 + proximityMean F R + Real.posLog (1 / τ)
  have hr : 0 < r := hα.trans (hαr.trans_le hr₀)
  have hg : 0 < R - r := sub_pos.mpr hrR
  have hm : 0 ≤ proximityMean F R := ValueDistribution.proximity_nonneg R
  have hP : 0 ≤ Real.posLog (1 / τ) := Real.posLog_nonneg
  have hb : 2 ≤ b := by dsimp [b]; linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEb : E ≤ 4 * b * (1 / (R - r)) := by
    rw [mul_one_div]
    apply (le_div_iff₀ hg).mpr
    dsimp [E, b]
    rw [add_mul, add_mul, div_mul_cancel₀ _ hg.ne']
    have hpg : Real.posLog (1 / τ) * (R - r) ≤ Real.posLog (1 / τ) := by
      nlinarith
    nlinarith
  obtain ⟨s, m, hN, hbound⟩ := local_log_derivative_poles hα hαr hr₀ hrR hR hF hτ hτF
  let N : ℝ := ((∑ a ∈ s, m a : ℕ) : ℝ)
  let D := logDerivativeRegularBound n α r R E N
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hD : 0 ≤ D := logDerivativeRegularBound_nonneg hα.le (hαr.trans_le hr₀) hrR hE hN0
  have hmero : MeromorphicOn (iteratedDeriv n (logDeriv F)) (sphere (0 : ℂ) |r|) := by
    apply meromorphicOn_iteratedDeriv
    intro z hz
    apply MeromorphicAt.logDeriv
    apply AnalyticAt.meromorphicAt
    apply hF.analyticOnNhd isOpen_ball
    have hnz : ‖z‖ = r := by simpa [abs_of_pos hr] using hz
    simpa [disk] using hnz ▸ hrR.trans hR
  have hpole : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|),
      ‖iteratedDeriv n (logDeriv F) z‖ ≤ D + (n.factorial : ℝ) *
        ∑ a ∈ s, (m a : ℝ) * ‖z - a‖ ^ (-((n + 1 : ℕ) : ℤ)) := by
    filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |r|),
      compl_finite_mem_codiscreteWithin s.finite_toSet] with z hz hzs
    have hzle : ‖z‖ ≤ r := by simpa [abs_of_pos hr] using hz.le
    have hh := hbound n z hzle hzs
    have he : -1 - (n : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
    rw [he] at hh
    convert hh using 1
    dsimp [D, logDerivativeRegularBound, N, E]
    rw [Finset.mul_sum]
    simp only [mul_left_comm (n.factorial : ℝ)]
    ring
  have hmean := hpoles (iteratedDeriv n (logDeriv F)) s m D (n.factorial : ℝ) r
    hD (Nat.cast_nonneg _) hr₀ hmero hpole
  obtain ⟨hNB, hDA⟩ := hpoly r R b E N hr₀ hrR hR hb hE hEb hN0 hN
  apply hmean.trans
  have ht : 1 ≤ 1 / (R - r) := (le_div_iff₀ hg).mpr (by linarith)
  simpa only [N, mul_assoc, mul_comm, mul_left_comm] using
    hgrowth D N b (1 / (R - r)) hD hN0 hb ht hDA hNB

end ModifiedCartan
