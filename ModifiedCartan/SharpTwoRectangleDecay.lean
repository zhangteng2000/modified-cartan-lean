import ModifiedCartan.SharpTwoAnalyticBounds
import ModifiedCartan.DiskSegmentLimits
import ModifiedCartan.DiskSegmentCompact
import ModifiedCartan.HarmonicRectangle
import ModifiedCartan.TwoPointHarnack
import ModifiedCartan.ExponentialDecay
import ModifiedCartan.Rescaling

noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics Complex InnerProductSpace Metric Set
namespace ModifiedCartan

/-- Actual Wronskian decay on one fixed rectangle after the symmetric segment
parameters converge. All bounds use the constructed growth setup. -/
theorem sharp_two_rectangle_decay {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ} {Ω : Set ℂ}
    (D : SharpTwoSetup A a s Ω)
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk 1))
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    {t : ℕ → ℝ} {ξ : ℕ → ℂ} {T : ℝ}
    (ht : ∀ n, 0 ≤ t n ∧ t n ≤ D.q) (hξ : ∀ n, ‖ξ n‖ = 1)
    (hT0 : 0 ≤ T) (hTq : T ≤ D.q) (hlim : Tendsto t atTop (𝓝 T))
    (hright : ∀ n, scaledDiskSegment (D.ρ n) (D.point 0 n) (ξ n) (t n) (t n : ℂ) = D.point 1 n) :
    ∃ h : ℝ, 0 < h ∧ T + 2 * h < 1 ∧ TendstoUniformlyOn
      (fun n z => wronskian (fun i => a i n)
        (scaledDiskSegment (D.ρ n) (D.point 0 n) (ξ n) (t n) z)) 0 atTop (segmentRectangle T h) := by
  let g := fun n => scaledDiskSegment (D.ρ n) (D.point 0 n) (ξ n) (t n)
  let M := fun n => unitGrowthMean (fun i => A i n) (D.ρ n)
  let U := fun n z => unitEnvelope (fun i => A i n) (D.ρ n) (g n z)
  let P := fun n z => U n z - Real.log ‖A 1 n (g n z)‖
  let Q := fun n z => U n z - Real.log ‖A 0 n (g n z)‖
  let V := fun n z => P n z + Q n z
  let d := D.r / D.α
  have hα : 0 < D.α := D.r_pos.trans D.r_lt
  have hd : 0 ≤ d := div_nonneg D.r_pos.le hα.le
  have hd1 : d < 1 := (div_lt_one hα).mpr D.r_lt
  have hq1 : D.q < 1 := D.q_lt.trans sharpRadius_lt_one
  have hρ0 : ∀ n, 0 < D.ρ n := fun n => hα.trans_le (D.radius n).1
  have hρ1 : ∀ n, D.ρ n < 1 := fun n => (D.radius n).2.trans (D.β_lt.trans D.v_lt)
  have hcenter : ∀ n, ‖D.point 0 n / (D.ρ n : ℂ)‖ ≤ d := by
    intro n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ0 n)]
    exact (div_le_div_of_nonneg_right
      (show ‖D.point 0 n‖ ≤ D.r by simpa only [mem_closedBall, dist_zero_right] using D.contained (D.point_mem 0 n))
      (hρ0 n).le).trans (div_le_div_of_nonneg_left D.r_pos.le hα (D.radius n).1)
  have htn : ∀ n, |t n| < 1 := fun n => by rw [abs_of_nonneg (ht n).1]; exact (ht n).2.trans_lt hq1
  have hg : ∀ n, AnalyticOnNhd ℂ (g n) (disk 1) := by
    intro n z hz
    change AnalyticAt ℂ (fun w => (D.ρ n : ℂ) * diskSegmentMap (D.point 0 n / (D.ρ n : ℂ)) (ξ n) (t n) w) z
    simpa only [Pi.mul_def] using analyticAt_const.mul
      (diskSegmentMap_analytic ((hcenter n).trans_lt hd1) (hξ n) (htn n) z hz)
  have hmap : ∀ n, MapsTo (g n) (disk 1) (disk (D.ρ n)) := by
    intro n z hz
    simpa only [g, scaledDiskSegment, mul_one] using (real_scale_mem_disk (hρ0 n)).mpr
      (diskSegmentMap_mem_disk ((hcenter n).trans_lt hd1) (hξ n) (htn n) hz)
  have hUh : ∀ n, HarmonicOnNhd (U n) (disk 1) := fun n =>
    harmonic_comp_analytic_to_ball (unitEnvelope_harmonic (fun i => hA i n) (hρ0 n).le (hρ1 n))
      isOpen_ball (hg n) (hmap n)
  have hPh : ∀ n, HarmonicOnNhd (P n) (disk 1) := fun n =>
    harmonic_comp_analytic_to_ball (unitEnvelope_deficit_harmonic (fun i => hA i n) (hρ0 n).le (hρ1 n) 1)
      isOpen_ball (hg n) (hmap n)
  have hQh : ∀ n, HarmonicOnNhd (Q n) (disk 1) := fun n =>
    harmonic_comp_analytic_to_ball (unitEnvelope_deficit_harmonic (fun i => hA i n) (hρ0 n).le (hρ1 n) 0)
      isOpen_ball (hg n) (hmap n)
  have hVh : ∀ n, HarmonicOnNhd (V n) (disk 1) := fun n => (hPh n).add (hQh n)
  have hUp : ∀ n z, z ∈ disk 1 → 0 ≤ U n z := fun n z hz =>
    (unitEnvelope_dominates (fun i => hA i n) (hρ0 n) (hρ1 n) (hmap n hz)).1
  have hPp : ∀ n z, z ∈ disk 1 → 0 ≤ P n z := fun n z hz => sub_nonneg.mpr
    ((unitEnvelope_dominates (fun i => hA i n) (hρ0 n) (hρ1 n) (hmap n hz)).2 1)
  have hQp : ∀ n z, z ∈ disk 1 → 0 ≤ Q n z := fun n z hz => sub_nonneg.mpr
    ((unitEnvelope_dominates (fun i => hA i n) (hρ0 n) (hρ1 n) (hmap n hz)).2 0)
  obtain ⟨ε, hε, hcomparison⟩ := real_segment_harmonic_comparison D.q_pos D.q_lt
  obtain ⟨p, hp, hp1, huniform⟩ := diskSegmentMap_uniform_norm hd hd1 D.q_pos.le hq1 D.q_pos.le hq1
  let c := (1 - p) / (1 + p)
  have hc : 0 < c := div_pos (sub_pos.mpr hp1) (by positivity)
  have hleft : ∀ n, g n ((-t n : ℝ) : ℂ) = D.point 0 n := by
    intro n
    dsimp [g, scaledDiskSegment]
    rw [diskSegmentMap_left, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hρ0 n).ne')]
  change ∀ n, g n (t n : ℂ) = D.point 1 n at hright
  have hsegment : ∀ᶠ n in atTop, ∀ x : ℝ, |x| ≤ t n →
      c * M n ≤ U n (x : ℂ) ∧ U n (x : ℂ) - V n (x : ℂ) ≤ -ε * U n (x : ℂ) + 2 * D.C₀ := by
    filter_upwards [D.controlled, D.failure] with n hn hfail
    intro x hx
    have hbound := hcomparison (U n) (P n) (Q n) (t n) D.C₀ (hUh n) (hPh n) (hQh n)
      (fun z hz => unitEnvelope_positive (fun i => hA i n) (hρ0 n) (hρ1 n) hn.1 (hmap n hz))
      (hPp n) (hQp n) (ht n).1 (ht n).2 D.C₀_nonneg ?_ ?_ x hx
    · refine ⟨?_, ?_⟩
      · apply unitEnvelope_scaled_lower (fun i => hA i n) (hρ0 n) (hρ1 n) hp.le hp1
        exact huniform _ _ _ _ (hcenter n) (hξ n) (ht n).1 (ht n).2
          (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx.trans (ht n).2)
      · dsimp [V]
        linarith
    · dsimp [Q]
      rw [hleft n]
      linarith [hfail 0]
    · dsimp [P]
      rw [hright n]
      linarith [hfail 1]
  obtain ⟨h, hh, hrect1, hnegative⟩ := harmonic_negative_rectangle hq1 hε
    (by linarith [D.C₀_nonneg] : 0 ≤ 2 * D.C₀) hTq ht hlim hUh hVh hUp
    (fun n z hz => add_nonneg (hPp n z hz) (hQp n z hz)) hsegment
  obtain ⟨B, hB, he, hW⟩ := sharp_two_analytic_bounds D hA ha hsum
  let e := fun n => Real.circleAverage (wronskianBoundaryError (fun i => a i n) B) 0 (D.ρ n)
  have he0 : ∀ n, 0 ≤ e n := fun n => Real.circleAverage_nonneg_of_nonneg
    (fun z _ => wronskianBoundaryError_nonneg (fun i => a i n) hB z)
  obtain ⟨p', hp', hp'1, hbound'⟩ := diskSegmentMap_uniform_norm hd hd1 D.q_pos.le hq1
    (by positivity : 0 ≤ T + 2 * h) hrect1
  refine ⟨h, hh, hrect1, ?_⟩
  apply uniform_zero_of_exp_negative_growth (c := ε * c / 2) (C := 2 * D.C₀)
    (k := (1 + p') / (1 - p')) (by positivity) D.growth he
  filter_upwards [hnegative, hW] with n hn hWn
  intro z hz
  have hz1 : z ∈ disk 1 := by simpa [disk] using (segmentRectangle_norm hz).trans hrect1
  have hgnorm := hbound' _ _ _ _ (hcenter n) (hξ n) (ht n).1 (ht n).2 (segmentRectangle_norm hz).le
  have hk := poisson_scaled_kernel_bound (hρ0 n) hp'.le hp'1 hgnorm
  have hkerr := mul_le_mul_of_nonneg_right hk (he0 n)
  have hmajor := hWn (g n z) (hmap n hz1)
  apply hmajor.trans (Real.exp_le_exp.mpr ?_)
  have hneg := hn z hz
  dsimp [U, V, P, Q] at hneg
  change (D.ρ n + ‖g n z‖) / (D.ρ n - ‖g n z‖) * e n ≤ (1 + p') / (1 - p') * e n at hkerr
  dsimp [e] at hkerr
  dsimp [M] at hneg
  linarith

end ModifiedCartan
