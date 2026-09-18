import ModifiedCartan.AngularGeometry
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

noncomputable section
set_option autoImplicit false
open Metric Set MeasureTheory Real
namespace ModifiedCartan

theorem abs_rpow_intervalIntegrable {p : ℝ} (hp : p < 1) :
    IntervalIntegrable (fun θ : ℝ => |θ| ^ (-p)) volume (-Real.pi) Real.pi := by
  have hi : IntervalIntegrable (fun θ : ℝ => |θ| ^ (-p)) volume 0 Real.pi := by
    apply (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -p)).congr_uIoo
    intro θ hθ
    rw [uIoo_of_lt Real.pi_pos] at hθ
    simp only [abs_of_pos hθ.1]
  have hn := (IntervalIntegrable.iff_comp_neg (by finiteness)).mp hi
  simp only [neg_zero, abs_neg] at hn
  exact hn.symm.trans hi

def angularPowerConstant (r₀ p : ℝ) : ℝ :=
  ∫ θ : ℝ in -Real.pi..Real.pi,
    (r₀ / 2) ^ (-p) + (r₀ / Real.pi) ^ (-p) * |θ| ^ (-p)

theorem angular_real_pole_integral {r₀ R A p : ℝ} (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hA : 0 ≤ A) (hp : 0 ≤ p) (hp1 : p < 1) :
    IntervalIntegrable (fun θ : ℝ => ‖circleMap 0 R θ - (A : ℂ)‖ ^ (-p))
      volume (-Real.pi) Real.pi ∧
    (∫ θ : ℝ in -Real.pi..Real.pi, ‖circleMap 0 R θ - (A : ℂ)‖ ^ (-p)) ≤
      angularPowerConstant r₀ p := by
  let f : ℝ → ℝ := fun θ => ‖circleMap 0 R θ - (A : ℂ)‖ ^ (-p)
  let g : ℝ → ℝ := fun θ => (r₀ / 2) ^ (-p) + (r₀ / Real.pi) ^ (-p) * |θ| ^ (-p)
  have hg : IntervalIntegrable g volume (-Real.pi) Real.pi :=
    intervalIntegrable_const.add ((abs_rpow_intervalIntegrable hp1).const_mul _)
  have hle : f ≤ᵐ[volume.restrict (uIoc (-Real.pi) Real.pi)] g := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (Measure.ae_ne volume 0)] with θ hθ hθ0
    rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at hθ
    have he := circle_inverse_power_domination (hr₀.trans_le hR) hA hp
      (abs_le.mpr ⟨hθ.1.le, hθ.2⟩) hθ0
    apply he.trans
    apply add_le_add
    · exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (div_le_div_of_nonneg_right hR (by norm_num)) (neg_nonpos.mpr hp)
    · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg θ) _)
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (div_le_div_of_nonneg_right hR Real.pi_pos.le) (neg_nonpos.mpr hp)
  have hfm : AEStronglyMeasurable f (volume.restrict (uIoc (-Real.pi) Real.pi)) := by
    dsimp [f]
    exact (Measurable.pow_const (by fun_prop) (-p)).aestronglyMeasurable
  have hf : IntervalIntegrable f volume (-Real.pi) Real.pi := by
    apply hg.mono_fun' hfm
    filter_upwards [hle] with θ hθ
    simpa only [f, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hθ
  refine ⟨hf, ?_⟩
  apply intervalIntegral.integral_mono_ae_restrict (by linarith [Real.pi_pos]) hf hg
  simpa only [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    restrict_Ioc_eq_restrict_Icc] using hle

theorem angularPowerConstant_nonneg {r₀ : ℝ} (hr₀ : 0 < r₀) (p : ℝ) :
    0 ≤ angularPowerConstant r₀ p := by
  apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
  intro θ _
  exact add_nonneg (Real.rpow_nonneg (by positivity) _)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (abs_nonneg θ) _))

/-- Uniform fractional-power integrability, including poles on the circle. -/
theorem angular_inverse_power_uniform {r₀ p : ℝ} (hr₀ : 0 < r₀) (hp : 0 ≤ p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), r₀ ≤ R → ∀ a : ℂ,
      CircleIntegrable (fun z => ‖z - a‖ ^ (-p)) 0 R ∧
      Real.circleAverage (fun z => ‖z - a‖ ^ (-p)) 0 R ≤ C := by
  refine ⟨(2 * Real.pi)⁻¹ * angularPowerConstant r₀ p,
    mul_nonneg (by positivity) (angularPowerConstant_nonneg hr₀ p), ?_⟩
  intro R hR a
  obtain ⟨hgi, hgint⟩ := angular_real_pole_integral hr₀ hR (norm_nonneg a) hp hp1
  let g : ℝ → ℝ := fun θ => ‖circleMap 0 R θ - (‖a‖ : ℂ)‖ ^ (-p)
  have hperiod : Function.Periodic g (2 * Real.pi) := by
    intro θ
    dsimp [g]
    rw [periodic_circleMap 0 R θ]
  have hgperiod : IntervalIntegrable g volume (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    convert hgi using 1 <;> ring
  have hgall := hperiod.intervalIntegrable (by positivity : 2 * Real.pi ≠ 0) hgperiod
  have hshift : IntervalIntegrable (fun θ => g (θ - a.arg)) volume 0 (2 * Real.pi) := by
    convert (hgall (-a.arg) (2 * Real.pi - a.arg)).comp_sub_right a.arg using 1 <;> ring
  have hrot (θ : ℝ) : g (θ - a.arg) = ‖circleMap 0 R θ - a‖ ^ (-p) := by
    dsimp [g]
    rw [← circle_distance_rotate R (θ - a.arg) a, sub_add_cancel]
  refine ⟨hshift.congr_uIoo (fun θ _ => hrot θ), ?_⟩
  have he : Real.circleAverage (fun z => ‖z - a‖ ^ (-p)) 0 R =
      (2 * Real.pi)⁻¹ * ∫ θ : ℝ in -Real.pi..Real.pi, g θ := by
    rw [Real.circleAverage_eq_integral_add (a.arg - Real.pi)]
    have hang (θ : ℝ) : θ + (a.arg - Real.pi) = (θ - Real.pi) + a.arg := by ring
    simp_rw [hang, circle_distance_rotate]
    change (2 * Real.pi)⁻¹ * (∫ θ : ℝ in 0..2 * Real.pi, g (θ - Real.pi)) = _
    rw [intervalIntegral.integral_comp_sub_right]
    congr 2 <;> ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hgint (by positivity)

/-- The simultaneous j/(2k) bounds appearing in `eq:angular-integrability`. -/
theorem angular_inverse_powers_finite {r₀ : ℝ} (hr₀ : 0 < r₀) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ R : ℝ, r₀ ≤ R → ∀ a : ℂ,
      CircleIntegrable (fun z => ‖z - a‖ ^ (-(j : ℝ) / (2 * k))) 0 R ∧
      Real.circleAverage (fun z => ‖z - a‖ ^ (-(j : ℝ) / (2 * k))) 0 R ≤ C := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hex : ∀ j : Fin (k + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, r₀ ≤ R → ∀ a : ℂ,
      CircleIntegrable (fun z => ‖z - a‖ ^ (-((j : ℕ) : ℝ) / (2 * k))) 0 R ∧
      Real.circleAverage (fun z => ‖z - a‖ ^ (-((j : ℕ) : ℝ) / (2 * k))) 0 R ≤ C := by
    intro j
    have hj : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast (show (j : ℕ) ≤ k by omega)
    simpa only [neg_div] using angular_inverse_power_uniform (p := ((j : ℕ) : ℝ) / (2 * k)) hr₀
      (div_nonneg (Nat.cast_nonneg _) (by positivity))
      ((div_lt_one (by positivity)).mpr (by linarith))
  choose C hC hbound using hex
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro j _hj hjk R hR a
  let i : Fin (k + 1) := ⟨j, by omega⟩
  obtain ⟨hi, hib⟩ := hbound i R hR a
  refine ⟨hi, hib.trans ?_⟩
  exact Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)

end ModifiedCartan
