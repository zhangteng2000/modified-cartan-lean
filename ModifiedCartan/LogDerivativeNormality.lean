import ModifiedCartan.HolomorphicLog
import ModifiedCartan.Montel
import ModifiedCartan.FailurePoints
import ModifiedCartan.Hurwitz
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- A bounded logarithmic derivative compares the modulus at any two points
of a disk, using a genuinely constructed holomorphic logarithm. -/
theorem unit_log_norm_difference_le {g : ℂ → ℂ} {T C : ℝ} (hT : 0 < T)
    (hg : IsHolomorphicUnit g (disk T)) (hbound : ∀ z ∈ disk T, ‖logDeriv g z‖ ≤ C)
    {z w : ℂ} (hz : z ∈ disk T) (hw : w ∈ disk T) :
    |Real.log ‖g z‖ - Real.log ‖g w‖| ≤ C * ‖z - w‖ := by
  obtain ⟨L, hL, hL0, he, hd⟩ := exists_holomorphic_log_on_disk hT hg.1 hg.2
  have hdiff : ∀ v ∈ disk T, DifferentiableAt ℂ L v :=
    fun v hv => hL.differentiableAt (isOpen_ball.mem_nhds hv)
  have hb : ∀ v ∈ disk T, ‖deriv L v‖ ≤ C := by
    intro v hv
    rw [hd v hv]
    exact hbound v hv
  have hnorm := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hb (convex_ball (0 : ℂ) T) hw hz
  have hreal : (L z - L w).re = Real.log ‖g z‖ - Real.log ‖g w‖ := by
    rw [Complex.sub_re, holomorphic_log_real_part he hz, holomorphic_log_real_part he hw]
  rw [← hreal]
  exact (Complex.abs_re_le_norm _).trans hnorm

theorem unit_norm_le_of_logDerivative_bound {g : ℂ → ℂ} {T C B : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hg : IsHolomorphicUnit g (disk T))
    (hbound : ∀ z ∈ disk T, ‖logDeriv g z‖ ≤ C)
    (hanchor : ∃ w ∈ disk T, ‖g w‖ ≤ B) :
    ∀ z ∈ disk T, ‖g z‖ ≤ B * Real.exp (2 * C * T) := by
  obtain ⟨w, hw, hwB⟩ := hanchor
  intro z hz
  have hdiff := (le_abs_self _).trans (unit_log_norm_difference_le hT hg hbound hz hw)
  have hnorm : ‖z - w‖ ≤ 2 * T := by
    have hzT : ‖z‖ < T := by simpa [disk] using hz
    have hwT : ‖w‖ < T := by simpa [disk] using hw
    exact (norm_sub_le _ _).trans (by linarith)
  have hlog : Real.log ‖g z‖ ≤ Real.log ‖g w‖ + 2 * C * T := by
    have hmul := mul_le_mul_of_nonneg_left hnorm hC
    nlinarith
  calc
    ‖g z‖ = Real.exp (Real.log ‖g z‖) := (Real.exp_log (norm_pos_iff.mpr (hg.2 z hz))).symm
    _ ≤ Real.exp (Real.log ‖g w‖ + 2 * C * T) := Real.exp_le_exp.mpr hlog
    _ = ‖g w‖ * Real.exp (2 * C * T) := by
      rw [Real.exp_add, Real.exp_log (norm_pos_iff.mpr (hg.2 w hw))]
    _ ≤ B * Real.exp (2 * C * T) := mul_le_mul_of_nonneg_right hwB (Real.exp_pos _).le

/-- A uniform logarithmic-derivative bound and one bounded value per function
supply an actual Montel subsequence on the entire disk. -/
theorem logDerivative_bounded_montel {g : ℕ → ℂ → ℂ} {T C B : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hg : ∀ n, IsHolomorphicUnit (g n) (disk T))
    (hbound : ∀ n z, z ∈ disk T → ‖logDeriv (g n) z‖ ≤ C)
    (hanchor : ∀ n, ∃ w ∈ disk T, ‖g n w‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G (disk T) ∧ CompactConvergence (fun n => g (φ n)) G (disk T) := by
  apply montel_subsequence isOpen_ball (fun n => (hg n).1)
  intro K hK hcompact
  exact ⟨B * Real.exp (2 * C * T), fun n z hz =>
    unit_norm_le_of_logDerivative_bound hT hC (hg n) (hbound n) (hanchor n) z (hK hz)⟩

/-- Failure of reciprocal decay supplies the moving anchor automatically. -/
theorem logDerivative_montel_of_no_reciprocal_decay {g : ℕ → ℂ → ℂ} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hg : ∀ n, IsHolomorphicUnit (g n) (disk T))
    (hbound : ∀ n z, z ∈ disk T → ‖logDeriv (g n) z‖ ≤ C)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => (g (φ n) z)⁻¹) (fun _ => 0) (disk T)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G (disk T) ∧ CompactConvergence (fun n => g (φ n)) G (disk T) := by
  obtain ⟨K, hK, hcK, B, hB, hevent⟩ := unit_failure_points isOpen_ball (fun n => (hg n).2) hno
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hanchor : ∀ n, ∃ w ∈ disk T, ‖g (N + n) w‖ ≤ Real.exp B := by
    intro n
    obtain ⟨w, hw, hb⟩ := hN (N + n) (by omega)
    exact ⟨w, hK hw, (Real.log_le_iff_le_exp (norm_pos_iff.mpr ((hg (N+n)).2 w (hK hw)))).mp hb⟩
  obtain ⟨ψ, hψ, G, hG, hlim⟩ := logDerivative_bounded_montel hT hC
    (fun n => hg (N + n)) (fun n => hbound (N + n)) hanchor
  exact ⟨fun n => N + ψ n, fun a b hab => Nat.add_lt_add_left (hψ hab) N, G, hG, hlim⟩

/-- Under the two-sided no-decay alternative the extracted limit is a unit,
which is the first normality branch in classical Cartan extraction. -/
theorem logDerivative_unit_limit_of_no_decay {g : ℕ → ℂ → ℂ} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hg : ∀ n, IsHolomorphicUnit (g n) (disk T))
    (hbound : ∀ n z, z ∈ disk T → ‖logDeriv (g n) z‖ ≤ C)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => (g (φ n) z)⁻¹) (fun _ => 0) (disk T))
    (hnozero : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n => g (φ n)) (fun _ => 0) (disk T)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ,
      IsHolomorphicUnit G (disk T) ∧ CompactConvergence (fun n => g (φ n)) G (disk T) := by
  obtain ⟨φ, hφ, G, hG, hc⟩ := logDerivative_montel_of_no_reciprocal_decay hT hC hg hbound hno
  have hnonzero : ∃ z ∈ disk T, G z ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hnozero
    refine ⟨φ, hφ, (compactConvergence_iff isOpen_ball).mpr ?_⟩
    exact ((compactConvergence_iff isOpen_ball).mp hc).congr_right (fun z hz => hn z hz)
  exact ⟨φ, hφ, G, ⟨hG, hurwitz_nonvanishing isOpen_ball
    (convex_ball (0 : ℂ) T).isPreconnected (fun n => hg (φ n)) hc hnonzero⟩, hc⟩

end ModifiedCartan
