import ModifiedCartan.WronskianCoefficientBounds

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

def jetUpperBound (m : ℕ) (r : ℝ) : ℝ :=
  1 + ∑ i : Fin m, ((i : ℕ).factorial : ℝ) / ((1 - r) / 2) ^ (i : ℕ)

theorem jetUpperBound_one_le (m : ℕ) {r : ℝ} (hr : r < 1) :
    1 ≤ jetUpperBound m r := by
  have hp : 0 ≤ ∑ i : Fin m, ((i : ℕ).factorial : ℝ) / ((1 - r) / 2) ^ (i : ℕ) :=
    Finset.sum_nonneg (fun i _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
  dsimp [jetUpperBound]
  linarith

theorem jet_le_upperBound {m : ℕ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hb : ∀ z ∈ disk 1, ‖F z‖ ≤ 1)
    {r : ℝ} (hr : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) (i : Fin m) :
    ‖iteratedDeriv (i : ℕ) F z‖ ≤ jetUpperBound m r := by
  have hi := iteratedDeriv_unit_disk_bound hF hb hr (i : ℕ) hz
  have hs := Finset.single_le_sum
    (s := Finset.univ) (f := fun i : Fin m => ((i : ℕ).factorial : ℝ) / ((1 - r) / 2) ^ (i : ℕ))
    (fun i _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)) (Finset.mem_univ i)
  dsimp [jetUpperBound]
  linarith

def wronskianCircleConstant (m : ℕ) (b : ℝ) : ℝ :=
  (m : ℝ) * (2 * Real.pi) * ((m.factorial : ℝ) * jetUpperBound m b ^ m)

theorem wronskianCircleConstant_pos {m : ℕ} (hm : 0 < m) {b : ℝ} (hb : b < 1) :
    0 < wronskianCircleConstant m b := by
  have hB := jetUpperBound_one_le m hb
  unfold wronskianCircleConstant
  positivity

/-- Quantitative control by a nonvanishing minor on one circle. -/
theorem wronskian_circle_lower_bound {n : ℕ} {g : Fin (n + 2) → ℂ → ℂ}
    {a ρ b v : ℝ} (ha : 0 ≤ a) (haρ : a < ρ) (hρb : ρ < b) (hb : b < 1) (hv : 0 < v)
    (hg : ∀ j, DifferentiableOn ℂ (g j) (disk 1))
    (hbound : ∀ j z, z ∈ disk 1 → ‖g j z‖ ≤ 1)
    (hV : ∀ z, ‖z‖ = ρ → v ≤ ‖wronskian (fun j : Fin (n + 1) => g j.castSucc) z‖) :
    leastCombinationNorm g a * v ^ 2 ≤
      wronskianCircleConstant (n + 1) b * diskSupNorm (wronskian g) b := by
  let Δ := diskSupNorm (wronskian g) b
  let B := jetUpperBound (n + 1) b
  let A := ((n + 1).factorial : ℝ) * B ^ (n + 1)
  let D := A * Δ / v ^ 2
  have hga : ∀ j, AnalyticOnNhd ℂ (g j) (disk 1) :=
    fun j => (hg j).analyticOnNhd isOpen_ball
  have hWcont := (wronskian_analyticOnNhd hga).continuousOn.mono (closedBall_subset_ball hb)
  have hΔ : 0 ≤ Δ := diskSupNorm_nonneg (by linarith) hWcont
  have hB : 1 ≤ B := jetUpperBound_one_le _ hb
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hA hΔ) (sq_nonneg _)
  have hsphere : ∀ z ∈ sphere (0 : ℂ) ρ, z ∈ disk 1 :=
    fun z hz => sphere_subset_ball (hρb.trans hb) hz
  have hVne : ∀ z ∈ sphere (0 : ℂ) ρ, wronskian (fun j : Fin (n + 1) => g j.castSucc) z ≠ 0 := by
    intro z hz
    exact norm_pos_iff.mp (hv.trans_le (hV z (by simpa using hz)))
  have hmain := combinationNorm_le_of_circle_coefficients
    (d := wronskianCoefficient g) ha haρ (hρb.trans hb) hD hg hbound
    (fun j z hz => (wronskianCoefficient_analyticAt hga (hsphere z hz) (hVne z hz) j).differentiableAt)
    (fun j z hz => wronskianCoefficient_deriv_norm_bound isOpen_ball hga (hsphere z hz) hB hv
      (fun i k => jet_le_upperBound (hg k.castSucc) (hbound k.castSucc) hb
        (by
          have he : ‖z‖ = ρ := by simpa using hz
          exact he.trans_le hρb.le) i)
      (le_csSup ((isCompact_closedBall (0 : ℂ) b).bddAbove_image hWcont.norm)
        (mem_image_of_mem _ (sphere_subset_closedBall.trans (closedBall_subset_closedBall hρb.le) hz)))
      (hV z (by simpa using hz)) j)
    (fun z hz => by
      have he := wronskianCoefficient_relation g (hVne z hz) (0 : Fin (n + 1))
      simpa only [Fin.val_zero, iteratedDeriv_zero, mul_comm] using he.symm)
  have hρ1 : ρ ≤ 1 := (hρb.trans hb).le
  have hle : leastCombinationNorm g a ≤ ((n + 1 : ℕ) : ℝ) * (2 * Real.pi * D) := by
    apply hmain.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _ = (2 * Real.pi * D) * ρ := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hρ1
  have hmul := (mul_le_mul_of_nonneg_right hle (sq_nonneg v))
  have he : ((n + 1 : ℕ) : ℝ) * (2 * Real.pi * D) * v ^ 2 =
      wronskianCircleConstant (n + 1) b * Δ := by
    dsimp [D, A, B, wronskianCircleConstant]
    field_simp
  rwa [he] at hmul

end ModifiedCartan
