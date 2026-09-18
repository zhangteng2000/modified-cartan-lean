import ModifiedCartan.WronskianCoefficients
import ModifiedCartan.CircleVariation
import ModifiedCartan.CombinationNorm
import Mathlib.Analysis.Complex.AbsMax

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

theorem wronskianCoefficient_deriv_norm_bound {n : ℕ} {g : Fin (n + 2) → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) {z : ℂ} (hz : z ∈ U)
    {B Δ v : ℝ} (hB : 1 ≤ B) (hv : 0 < v)
    (hentries : ∀ i j : Fin (n + 1), ‖iteratedDeriv (i : ℕ) (g j.castSucc) z‖ ≤ B)
    (hW : ‖wronskian g z‖ ≤ Δ)
    (hV : v ≤ ‖wronskian (fun j : Fin (n + 1) => g j.castSucc) z‖) (j : Fin (n + 1)) :
    ‖deriv (wronskianCoefficient g j) z‖ ≤
      ((n + 1).factorial : ℝ) * B ^ (n + 1) * Δ / v ^ 2 := by
  let A := ((n + 1).factorial : ℝ) * B ^ (n + 1)
  let V := ‖wronskian (fun j : Fin (n + 1) => g j.castSucc) z‖
  have hVpos : 0 < V := hv.trans_le hV
  have hVne := norm_ne_zero_iff.mp hVpos.ne'
  have hΔ : 0 ≤ Δ := (norm_nonneg _).trans hW
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
  have hinv : ‖(minorJetMatrix g z)⁻¹ j (Fin.last n)‖ ≤ A / V :=
    matrix_inv_norm_bound (minorJetMatrix g z) hB hentries j (Fin.last n)
  rw [wronskianCoefficient_deriv hU hg hz hVne j, norm_mul, norm_div]
  change _ * (‖wronskian g z‖ / V) ≤ A * Δ / v ^ 2
  calc
    _ ≤ (A / V) * (Δ / V) := mul_le_mul hinv
      (div_le_div_of_nonneg_right hW hVpos.le)
      (div_nonneg (norm_nonneg _) hVpos.le) (div_nonneg hA hVpos.le)
    _ = (A * Δ) / V ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hA hΔ) (sq_pos_of_pos hv)
      (by dsimp [V]; nlinarith)

/-- The circle-variation and maximum-principle step of the Wronskian induction. -/
theorem combinationNorm_le_of_circle_coefficients {m : ℕ}
    {g : Fin (m + 1) → ℂ → ℂ} {d : Fin m → ℂ → ℂ}
    {a ρ D : ℝ} (ha : 0 ≤ a) (haρ : a < ρ) (hρ1 : ρ < 1) (hD : 0 ≤ D)
    (hg : ∀ j, DifferentiableOn ℂ (g j) (disk 1))
    (hbound : ∀ j z, z ∈ disk 1 → ‖g j z‖ ≤ 1)
    (hd : ∀ j z, z ∈ sphere (0 : ℂ) ρ → DifferentiableAt ℂ (d j) z)
    (hderiv : ∀ j z, z ∈ sphere (0 : ℂ) ρ → ‖deriv (d j) z‖ ≤ D)
    (hrel : ∀ z ∈ sphere (0 : ℂ) ρ, g (Fin.last m) z = ∑ j, d j z * g j.castSucc z) :
    leastCombinationNorm g a ≤ (m : ℝ) * (2 * Real.pi * ρ * D) := by
  classical
  have hρ : 0 < ρ := ha.trans_lt haρ
  let c : Fin (m + 1) → ℂ := Fin.snoc (fun j => -d j (ρ : ℂ)) 1
  let G : ℂ → ℂ := fun z => ∑ j, c j * g j z
  have hG : DifferentiableOn ℂ G (disk 1) :=
    DifferentiableOn.fun_sum (fun j _ => (hg j).const_mul (c j))
  have hc : 1 ≤ coefficientNormSq c := by
    have hh : 0 ≤ ∑ j : Fin m, ‖d j (ρ : ℂ)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    simpa [coefficientNormSq, c, Fin.sum_univ_castSucc] using (le_add_of_nonneg_left hh : (1 : ℝ) ≤ _ + 1)
  have hGcircle : ∀ z ∈ sphere (0 : ℂ) ρ, ‖G z‖ ≤ (m : ℝ) * (2 * Real.pi * ρ * D) := by
    intro z hz
    have hzU : z ∈ disk 1 := sphere_subset_ball hρ1 hz
    have he : G z = ∑ j : Fin m, (d j z - d j (ρ : ℂ)) * g j.castSucc z := by
      simp only [G, c, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, one_mul, neg_mul]
      rw [hrel z hz]
      simp only [Finset.sum_neg_distrib, Finset.sum_sub_distrib, sub_mul]
      ring
    rw [he]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : Fin m, 2 * Real.pi * ρ * D := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hbound j.castSucc z hzU)).trans
          (circle_variation_bound hρ hD (hd j) (hderiv j) hz)
      _ = _ := by simp
  have hGdisk : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖G z‖ ≤ (m : ℝ) * (2 * Real.pi * ρ * D) := by
    have hGreg : DifferentiableOn ℂ G (closure (ball (0 : ℂ) ρ)) := by
      rw [closure_ball _ hρ.ne']
      exact hG.mono (closedBall_subset_ball hρ1)
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hGreg.diffContOnCl
    · simpa only [frontier_ball _ hρ.ne'] using hGcircle
    · rwa [closure_ball _ hρ.ne']
  have hga : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) a) :=
    fun j => (hg j).continuousOn.mono (closedBall_subset_ball (haρ.trans hρ1))
  apply (leastCombinationNorm_le_unnormalized (by omega) ha hga c hc).trans
  apply csSup_le (Nonempty.image _ ⟨0, by simp [ha]⟩)
  rintro v ⟨z, hz, rfl⟩
  exact hGdisk z (closedBall_subset_closedBall haρ.le hz)

end ModifiedCartan
