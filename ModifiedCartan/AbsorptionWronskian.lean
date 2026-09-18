import ModifiedCartan.WronskianScaling
import ModifiedCartan.WronskianExponents
import ModifiedCartan.Rescaling

noncomputable section
set_option autoImplicit false
open Metric Set Real
namespace ModifiedCartan

theorem diskSupNorm_congr {f g : ℂ → ℂ} {r : ℝ}
    (he : EqOn f g (closedBall (0 : ℂ) r)) : diskSupNorm f r = diskSupNorm g r := by
  unfold diskSupNorm
  congr 1
  ext v
  constructor <;> rintro ⟨z, hz, hv⟩ <;> refine ⟨z, hz, ?_⟩
  · change ‖g z‖ = v
    rwa [← he hz]
  · change ‖f z‖ = v
    rwa [he hz]

/-- A quantitative Wronskian lower bound at an actual maximizing point after
both normalizations used by the manuscript. The input scale and its determinant
exponent are retained exactly. -/
theorem absorption_wronskian_point {K : ℕ → ℝ} (hK : WronskianExponents K)
    {m : ℕ} (hm : 1 ≤ m) {η ell : ℝ} (hη : 0 < η) (hη1 : 4 * η < 1)
    (hell : 0 < ell) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin m → ℂ → ℂ) (L : ℝ),
      (∀ j, DifferentiableOn ℂ (a j) (disk 1)) →
      (∀ j z, ‖z‖ ≤ 4 * η → ‖a j z‖ ≤ Real.exp L) →
      ell ≤ leastCombinationNorm a η →
      ∃ w : ℂ, ‖w‖ ≤ 2 * η ∧ wronskian a w ≠ 0 ∧
        -(K m - (m : ℝ)) * L + Real.log c + K m * Real.log ell -
          ((m * (m - 1) / 2 : ℕ) : ℝ) * Real.log (4 * η) ≤ Real.log ‖wronskian a w‖ := by
  obtain ⟨hKm, c, hc, hquant⟩ := hK m hm
  refine ⟨c, hc, ?_⟩
  intro a L ha hbound hgap
  let scale : ℂ → ℂ := fun z => ((4 * η : ℝ) : ℂ) * z
  let g : Fin m → ℂ → ℂ := fun j z => (Real.exp (-L) : ℂ) * a j (scale z)
  have hscale : Differentiable ℂ scale := by dsimp [scale]; fun_prop
  have hscaleMem : ∀ z ∈ disk 1, scale z ∈ disk 1 := by
    intro z hz
    have hz4 : scale z ∈ disk (4 * η) := by
      simpa only [mul_one] using (real_scale_mem_disk (by positivity : 0 < 4 * η)).mpr hz
    exact ball_subset_ball hη1.le hz4
  have hg : ∀ j, DifferentiableOn ℂ (g j) (disk 1) :=
    fun j => ((ha j).comp hscale.differentiableOn hscaleMem).const_mul _
  have hgnorm : ∀ j z, z ∈ disk 1 → ‖g j z‖ ≤ 1 := by
    intro j z hz
    have hz4 : ‖scale z‖ ≤ 4 * η := by
      have hh := (real_scale_mem_disk (by positivity : 0 < 4 * η)).mpr hz
      have hh' : ‖scale z‖ < 4 * η := by
        simpa only [mul_one, disk, mem_ball, dist_zero_right] using hh
      exact hh'.le
    change ‖(Real.exp (-L) : ℂ) * a j (scale z)‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-L) * Real.exp L := mul_le_mul_of_nonneg_left (hbound j (scale z) hz4) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hcompcont : ∀ j, ContinuousOn (fun z => a j (scale z)) (closedBall (0 : ℂ) (1 / 4)) :=
    fun j => ((ha j).comp hscale.differentiableOn hscaleMem).continuousOn.mono
      (closedBall_subset_ball (by norm_num : (1 / 4 : ℝ) < 1))
  have hleast : leastCombinationNorm g (1 / 4) = Real.exp (-L) * leastCombinationNorm a η := by
    rw [leastCombinationNorm_const_mul (by omega) (by norm_num) hcompcont]
    change ‖(Real.exp (-L) : ℂ)‖ * leastCombinationNorm
      (fun j z => a j (((4 * η : ℝ) : ℂ) * z)) (1 / 4) = _
    rw [leastCombinationNorm_input_scale a (by positivity : 0 < 4 * η)]
    norm_num only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    congr 2
    ring
  have hlower : c * (Real.exp (-L) * ell) ^ (K m) ≤ diskSupNorm (wronskian g) (1 / 2) := by
    apply le_trans _ (hquant g hg hgnorm)
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.rpow_le_rpow (by positivity) _ ((Nat.cast_nonneg m).trans hKm)
    rw [hleast]
    exact mul_le_mul_of_nonneg_left hgap (Real.exp_pos _).le
  let d := m * (m - 1) / 2
  have hW : AnalyticOnNhd ℂ (wronskian a) (disk 1) :=
    wronskian_analyticOnNhd (fun j => (ha j).analyticOnNhd isOpen_ball)
  have hcompW : ContinuousOn (fun z => wronskian a (scale z)) (closedBall (0 : ℂ) (1 / 2)) :=
    (hW.continuousOn.comp hscale.continuous.continuousOn hscaleMem).mono
      (closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1))
  have hWscale : diskSupNorm (wronskian g) (1 / 2) =
      (Real.exp (-L)) ^ m * (4 * η) ^ d * diskSupNorm (wronskian a) (2 * η) := by
    have he : EqOn (wronskian g)
        (fun z => (Real.exp (-L) : ℂ) ^ m * ((4 * η : ℝ) : ℂ) ^ d * wronskian a (scale z))
        (closedBall (0 : ℂ) (1 / 2)) := by
      intro z hz
      change wronskian (fun j w => (Real.exp (-L) : ℂ) * a j (scale w)) z = _
      rw [wronskian_common_const, wronskian_comp_mul]
      · simp only [scale, d, mul_assoc]
      · intro j
        exact (ha j).analyticOnNhd isOpen_ball _
          (hscaleMem z (closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1) hz))
    rw [diskSupNorm_congr he, diskSupNorm_const_mul (by norm_num) hcompW]
    change ‖(Real.exp (-L) : ℂ) ^ m * ((4 * η : ℝ) : ℂ) ^ d‖ *
      diskSupNorm (fun z => wronskian a (((4 * η : ℝ) : ℂ) * z)) (1 / 2) = _
    rw [diskSupNorm_input_scale _ (by positivity : 0 < 4 * η)]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos hη]
    congr 2 <;> ring
  obtain ⟨w, hw, hmax⟩ := diskSupNorm_attained (by positivity : 0 ≤ 2 * η)
    (hW.continuousOn.mono (closedBall_subset_ball (by linarith : 2 * η < 1)))
  rw [hWscale, hmax] at hlower
  have hleft : 0 < c * (Real.exp (-L) * ell) ^ (K m) := by positivity
  have hright := hleft.trans_le hlower
  have hWpos : 0 < ‖wronskian a w‖ :=
    (mul_pos_iff.mp hright).elim (fun h => h.2) (fun h => False.elim (not_lt_of_ge (by positivity) h.1))
  refine ⟨w, by simpa using hw, norm_pos_iff.mp hWpos, ?_⟩
  have hlog := Real.log_le_log hleft hlower
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos (mul_pos (Real.exp_pos _) hell) _).ne',
    Real.log_rpow (mul_pos (Real.exp_pos _) hell),
    Real.log_mul (Real.exp_ne_zero _) hell.ne', Real.log_exp,
    Real.log_mul (mul_pos (pow_pos (Real.exp_pos _) m) (pow_pos (by positivity : 0 < 4 * η) d)).ne' hWpos.ne',
    Real.log_mul (pow_ne_zero _ (Real.exp_ne_zero _)) (pow_ne_zero _ (by positivity : 4 * η ≠ 0)),
    Real.log_pow, Real.log_pow, Real.log_exp] at hlog
  dsimp [d] at hlog
  linarith

/-- Uniform form of the logarithmic point lower bound, with a constant independent
of the sequence index and the growth parameter M. -/
theorem absorption_wronskian_growth_lower {K : ℕ → ℝ} (hK : WronskianExponents K)
    {m : ℕ} (hm : 1 ≤ m) {η ell C₀ : ℝ} (hη : 0 < η) (hη1 : 4 * η < 1)
    (hell : 0 < ell) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (a : Fin m → ℂ → ℂ) (M : ℝ), 0 ≤ M →
      (∀ j, DifferentiableOn ℂ (a j) (disk 1)) →
      (∀ j z, ‖z‖ ≤ 4 * η → ‖a j z‖ ≤ Real.exp (64 * η * M + C₀)) →
      ell ≤ leastCombinationNorm a η →
      ∃ w : ℂ, ‖w‖ ≤ 2 * η ∧ wronskian a w ≠ 0 ∧
        -64 * K m * η * M - D ≤ Real.log ‖wronskian a w‖ := by
  obtain ⟨c, hc, hpoint⟩ := absorption_wronskian_point hK hm hη hη1 hell
  let b := -(K m - (m : ℝ)) * C₀ + Real.log c + K m * Real.log ell -
    ((m * (m - 1) / 2 : ℕ) : ℝ) * Real.log (4 * η)
  refine ⟨|b|, abs_nonneg _, ?_⟩
  intro a M hM ha hbound hgap
  obtain ⟨w, hw, hnz, hlower⟩ := hpoint a (64 * η * M + C₀) ha hbound hgap
  refine ⟨w, hw, hnz, ?_⟩
  have hb : -|b| ≤ b := neg_abs_le b
  dsimp [b] at hb
  have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  nlinarith [mul_nonneg hmnonneg (mul_nonneg hη.le hM)]

end ModifiedCartan
