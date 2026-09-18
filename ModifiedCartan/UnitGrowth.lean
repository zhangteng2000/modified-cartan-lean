import ModifiedCartan.HarmonicGrowth
import ModifiedCartan.PoissonHarnack
import ModifiedCartan.AbsorptionPreparations

noncomputable section
set_option autoImplicit false
open Filter Topology Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

def unitGrowthMean {m : ℕ} (A : Fin m → ℂ → ℂ) (r : ℝ) : ℝ :=
  harmonicGrowthMean (fun i z => Real.log ‖A i z‖) r

theorem unit_log_harmonic {A : ℂ → ℂ} (hA : IsHolomorphicUnit A (disk 1)) :
    HarmonicOnNhd (fun z => Real.log ‖A z‖) (disk 1) :=
  fun z hz => (hA.1.analyticOnNhd isOpen_ball z hz).harmonicAt_log_norm (hA.2 z hz)

theorem norm_le_exp_unitGrowthMean {m : ℕ} {A : Fin m → ℂ → ℂ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    {w : ℂ} (hw : w ∈ disk R) (i : Fin m) :
    ‖A i w‖ ≤ Real.exp ((R + ‖w‖) / (R - ‖w‖) * unitGrowthMean A R) := by
  let u := fun i z => Real.log ‖A i z‖
  let v := fun z => maxWithZero (fun i => u i z)
  have hu : ∀ i, HarmonicOnNhd (u i) (closedBall (0 : ℂ) R) :=
    fun i => (unit_log_harmonic (hA i)).mono (closedBall_subset_ball hR1)
  have hv : CircleIntegrable v 0 R := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hR]
    exact (continuousOn_maxWithZero (fun i => (hu i).continuousOn)).mono sphere_subset_closedBall
  have h1 := (le_maxWithZero (fun i => u i w) i).trans (harmonic_max_le_poissonExtension hR hu hw)
  have h2 := (poissonExtension_harnack_bounds hv (fun z _ => maxWithZero_nonneg _) hw).2
  rw [poissonExtension_zero hR hv] at h2
  have hnorm : 0 < ‖A i w‖ := norm_pos_iff.mpr
    ((hA i).2 w (ball_subset_ball hR1.le hw))
  rw [← Real.exp_log hnorm]
  exact Real.exp_le_exp.mpr (h1.trans h2)

theorem unitGrowthMean_continuousOn {m : ℕ} {A : Fin m → ℂ → ℂ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) :
    ContinuousOn (unitGrowthMean A) (Ico 0 1) :=
  harmonicGrowthMean_continuousOn (fun i => unit_log_harmonic (hA i))

theorem unitGrowthMean_monotoneOn {m : ℕ} {A : Fin m → ℂ → ℂ}
    (hA : ∀ i, IsHolomorphicUnit (A i) (disk 1)) :
    MonotoneOn (unitGrowthMean A) (Ico 0 1) :=
  harmonicGrowthMean_monotoneOn (fun i => unit_log_harmonic (hA i))

/-- The diverging-growth assertion in the manuscript absorption proof. -/
theorem unitGrowthMean_tendsto_atTop {m : ℕ} (hm : 0 < m)
    (A a : Family m) (s : ℂ → ℂ) (hA : UnitFamily A)
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) (fun _ => 0) (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    (hsne : ∃ z ∈ disk 1, s z ≠ 0) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Tendsto (fun n => unitGrowthMean (fun i => A i n) r) atTop atTop := by
  have hs := compactConvergence_holomorphic isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
  obtain ⟨w, hw, hsw⟩ := nontrivial_on_smaller_disk hs hr hr1.le hsne
  have hwunit : w ∈ disk 1 := ball_subset_ball hr1.le hw
  have hwnorm : ‖w‖ < r := by simpa [disk] using hw
  have hsw0 : 0 < ‖s w‖ := norm_pos_iff.mpr hsw
  let c := ‖s w‖ / 2
  let q := (r + ‖w‖) / (r - ‖w‖)
  have hc : 0 < c := half_pos hsw0
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hml : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hsumlower : ∀ᶠ n in atTop, c < ‖∑ i, a i n w‖ := by
    exact (compactConvergence_pointwise hsum hwunit).norm.eventually
      (lt_mem_nhds (half_lt_self hsw0))
  apply Filter.tendsto_atTop.mpr
  intro B
  let D := Real.exp (q * B)
  let ε := c / (2 * (m : ℝ) * D)
  have hD : 0 < D := Real.exp_pos _
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hratios : ∀ᶠ n in atTop, ∀ i, ‖a i n w / A i n w‖ < ε := by
    apply eventually_all.mpr
    intro i
    have hh := (compactConvergence_pointwise (hsmall i) hwunit).norm
    rw [norm_zero] at hh
    exact hh.eventually (gt_mem_nhds hε)
  filter_upwards [hsumlower, hratios] with n hn hratio
  by_contra hnB
  have hMB : unitGrowthMean (fun i => A i n) r ≤ B := (lt_of_not_ge hnB).le
  have hnormA : ∀ i, ‖A i n w‖ ≤ D := by
    intro i
    apply (norm_le_exp_unitGrowthMean (fun i => hA i n) hr hr1 hw i).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hMB hq)
  have hnorma : ∀ i, ‖a i n w‖ ≤ ε * D := by
    intro i
    calc
      _ = ‖a i n w / A i n w‖ * ‖A i n w‖ := by
        rw [← norm_mul, div_mul_cancel₀ _ ((hA i n).2 w hwunit)]
      _ ≤ ε * D := mul_le_mul (hratio i).le (hnormA i) (norm_nonneg _) hε.le
  have hsumupper : ‖∑ i, a i n w‖ ≤ c / 2 := by
    calc
      _ ≤ ∑ i, ‖a i n w‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin m, ε * D := Finset.sum_le_sum (fun i _ => hnorma i)
      _ = c / 2 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp [ε]; field_simp
  linarith

end ModifiedCartan
