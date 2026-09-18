import ModifiedCartan.AngularIntegrals
import ModifiedCartan.FractionalPowers
import ModifiedCartan.CircleExceptional
import ModifiedCartan.ProximityMoment

noncomputable section
set_option autoImplicit false
open Filter Metric Set Real
namespace ModifiedCartan

theorem logarithmic_mean_of_pole_bound {r₀ p : ℝ} {j : ℕ}
    (hr₀ : 0 < r₀) (hp : 0 < p) (hp1 : p ≤ 1) (hjp : (j : ℝ) * p < 1) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (f : ℂ → ℂ) (s : Finset ℂ) (m : ℂ → ℕ) (D C R : ℝ),
      0 ≤ D → 0 ≤ C → r₀ ≤ R → MeromorphicOn f (sphere (0 : ℂ) |R|) →
      (∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|),
        ‖f z‖ ≤ D + C * ∑ a ∈ s, (m a : ℝ) * ‖z - a‖ ^ (-(j : ℤ))) →
      proximityMean f R ≤ (1 / p) * Real.log
        (1 + D ^ p + C ^ p * ((∑ a ∈ s, m a : ℕ) : ℝ) * C₀) := by
  obtain ⟨C₀, hC₀, hangular⟩ := angular_inverse_power_uniform hr₀
    (mul_nonneg (Nat.cast_nonneg j) hp.le) hjp
  refine ⟨C₀, hC₀, ?_⟩
  intro f s m D C R hD hC hR hf hbound
  let v : ℂ → ℝ := fun z => ∑ a ∈ s, (m a : ℝ) * ‖z - a‖ ^ (-(j : ℝ) * p)
  let g : ℂ → ℝ := (fun _ => D ^ p) + C ^ p • v
  have hi : ∀ a ∈ s, CircleIntegrable (fun z => ‖z - a‖ ^ (-(j : ℝ) * p)) 0 R := by
    intro a _
    simpa only [neg_mul] using (hangular R hR a).1
  have he : v = ∑ a ∈ s, (m a : ℝ) • (fun z => ‖z - a‖ ^ (-(j : ℝ) * p)) := by
    ext z
    simp [v]
  have hv : CircleIntegrable v 0 R := by
    rw [he]
    apply CircleIntegrable.sum s
    intro a ha
    exact (hi a ha).const_smul
  have hg : CircleIntegrable g 0 R := (circleIntegrable_const _ _ _).add hv.const_smul
  have hpow : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|), ‖f z‖ ^ p ≤ g z := by
    filter_upwards [hbound] with z hz
    have hsum : 0 ≤ ∑ a ∈ s, (m a : ℝ) * ‖z - a‖ ^ (-(j : ℤ)) :=
      Finset.sum_nonneg (fun a _ => mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (norm_nonneg _) _))
    calc
      _ ≤ (D + C * ∑ a ∈ s, (m a : ℝ) * ‖z - a‖ ^ (-(j : ℤ))) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) hz hp.le
      _ ≤ D ^ p + (C * ∑ a ∈ s, (m a : ℝ) * ‖z - a‖ ^ (-(j : ℤ))) ^ p :=
        Real.rpow_add_le_add_rpow hD (mul_nonneg hC hsum) hp.le hp1
      _ ≤ g z := by
        rw [Real.mul_rpow hC hsum]
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left
          (weighted_pole_sum_rpow_bound s m (fun a => ‖z - a‖) (fun a _ => norm_nonneg _) j hp hp1)
          (Real.rpow_nonneg hC p)
  have hRne : R ≠ 0 := (hr₀.trans_le hR).ne'
  have hfint := circleIntegrable_norm_rpow_of_codiscrete_le hRne hf hg hpow
  have hmean := circleAverage_mono_codiscrete hRne hfint hg hpow
  have hvmean : Real.circleAverage v 0 R ≤ ((∑ a ∈ s, m a : ℕ) : ℝ) * C₀ := by
    rw [he, Real.circleAverage_sum (fun a ha => (hi a ha).const_smul)]
    simp only [Real.circleAverage_smul, smul_eq_mul, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simpa only [neg_mul] using (hangular R hR a).2
  have hgmean : Real.circleAverage g 0 R ≤ D ^ p + C ^ p * (((∑ a ∈ s, m a : ℕ) : ℝ) * C₀) := by
    dsimp [g]
    rw [Real.circleAverage_add (circleIntegrable_const _ _ _) hv.const_smul,
      Real.circleAverage_const, Real.circleAverage_smul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hvmean (Real.rpow_nonneg hC p))
  apply (proximity_le_log_moment hp hf.circleIntegrable_posLog_norm hfint).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.log_le_log
  · have hh : 0 ≤ Real.circleAverage (fun z => ‖f z‖ ^ p) 0 R :=
      Real.circleAverage_nonneg_of_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  · have hh := hmean.trans hgmean
    nlinarith only [hh]

end ModifiedCartan
