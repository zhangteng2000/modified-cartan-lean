import ModifiedCartan.LogPoisson
import ModifiedCartan.Radii
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics Metric Real
namespace ModifiedCartan

theorem absorption_poisson_constants {η t : ℝ} (hη : 0 ≤ η) (hη64 : η ≤ 1 / 64)
    (ht : 0 ≤ t) (htη : t ≤ 4 * η) :
    let q := (1 + t) / (1 - t)
    1 ≤ q ∧ q ≤ 2 ∧ 0 ≤ q ^ 2 - 1 ∧ q ^ 2 - 1 ≤ 20 * η := by
  have ht16 : t ≤ 1 / 16 := by linarith
  have hden : 0 < 1 - t := by linarith
  have hq1 : 1 ≤ (1 + t) / (1 - t) := (le_div_iff₀ hden).mpr (by linarith)
  have hq2 : (1 + t) / (1 - t) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  have hq0 : 0 ≤ ((1 + t) / (1 - t)) ^ 2 - 1 := by nlinarith
  refine ⟨hq1, hq2, hq0, ?_⟩
  have he : (((1 + t) / (1 - t)) ^ 2 - 1) * (1 - t) ^ 2 = 4 * t := by
    field_simp
    ring
  have hd2 : (225 / 256 : ℝ) ≤ (1 - t) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hd2 hq0
  nlinarith

theorem wronskian_mean_lower_from_point {W : ℂ → ℂ} {ρ η M D E K m : ℝ}
    (hρ : 1 / 2 ≤ ρ) (hη : 0 ≤ η) (hη64 : η ≤ 1 / 64)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hE : 0 ≤ E) (hK : 0 ≤ K) (hm : 1 ≤ m)
    (hW : AnalyticOnNhd ℂ W (closedBall 0 ρ)) {w : ℂ}
    (hw : ‖w‖ ≤ 2 * η) (hnz : W w ≠ 0)
    (hlower : -64 * K * η * M - D ≤ Real.log ‖W w‖)
    (hpositive : proximityMean W ρ ≤ (m - 1) * M + E) :
    -(128 * K + 20 * m) * η * M - 2 * D - E ≤
      Real.circleAverage (fun z => Real.log ‖W z‖) 0 ρ := by
  have hρ0 : 0 < ρ := by linarith
  have hwρ : w ∈ disk ρ := by
    have : ‖w‖ < ρ := by linarith
    simpa [disk] using this
  let t := ‖w‖ / ρ
  let q := (1 + t) / (1 - t)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htη : t ≤ 4 * η := by
    apply (div_le_iff₀ hρ0).mpr
    nlinarith
  obtain ⟨hq1, hq2, hq0, hqη⟩ := absorption_poisson_constants hη hη64 ht htη
  have hp := poissonMeanEstimate_proved W ρ w hW hwρ hnz
  change q * Real.log ‖W w‖ - (q ^ 2 - 1) * proximityMean W ρ ≤ _ at hp
  change 1 ≤ q at hq1
  change q ≤ 2 at hq2
  change 0 ≤ q ^ 2 - 1 at hq0
  change q ^ 2 - 1 ≤ 20 * η at hqη
  have hlow0 : 0 ≤ 64 * K * η * M + D := by positivity
  have hl := mul_le_mul_of_nonneg_left hlower (by linarith : 0 ≤ q)
  have htwo := mul_le_mul_of_nonneg_right hq2 hlow0
  have hb0 : 0 ≤ (m - 1) * M + E := by positivity
  have he := mul_le_mul hqη hpositive (ValueDistribution.proximity_nonneg _) (by positivity : 0 ≤ 20 * η)
  have heE : 20 * η * E ≤ E := by nlinarith
  have hmM : 0 ≤ η * M := mul_nonneg hη hM
  nlinarith

/-- The last contradiction in the absorption induction, retaining the exact
1/8 bound and allowing an arbitrary genuine little-o error. -/
theorem absorption_growth_contradiction {M E I : ℕ → ℝ} {K m δ D : ℝ}
    (hm : 0 < m) (hK : m ≤ K) (hδ : δ ≤ 1 / (1024 * (K + m)))
    (hM : Tendsto M atTop atTop) (hE : E =o[atTop] M)
    (hupper : ∀ᶠ n in atTop, I n ≤ (8 * m * δ - 1) * M n + E n)
    (hlower : ∀ᶠ n in atTop,
      -(128 * K + 20 * m) / (1024 * (K + m)) * M n - D - E n ≤ I n) : False := by
  have hcoeff := absorption_constant_bound hm hK hδ
  have he := hE.bound (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨n, ⟨⟨⟨⟨hnM, hnD⟩, hnE⟩, hnU⟩, hnL⟩⟩ := (hM.eventually (eventually_gt_atTop (0 : ℝ)) |>.and
    (hM.eventually (eventually_gt_atTop (2 * |D|))) |>.and he |>.and hupper |>.and hlower).exists
  have hEbound : E n ≤ (1 / 8 : ℝ) * M n := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, abs_of_pos hnM] using hnE
  have hcmul := mul_le_mul_of_nonneg_right hcoeff hnM.le
  have hDabs := le_abs_self D
  simp only [neg_div] at hnL
  ring_nf at hnL hnU hcmul
  linarith only [hnL, hnU, hcmul, hEbound, hnD, hDabs, hnM]

end ModifiedCartan
