import ModifiedCartan.AbsorptionGap
import ModifiedCartan.FiniteFailurePoints
import ModifiedCartan.AbsorptionGrowth
import ModifiedCartan.AbsorptionEnvelope
import ModifiedCartan.AbsorptionWronskian
import ModifiedCartan.AbsorptionComparison
import ModifiedCartan.ConvergenceJets
import ModifiedCartan.BoundaryErrorLimit

noncomputable section
set_option autoImplicit false
open Filter Topology Asymptotics Metric Set Real
namespace ModifiedCartan

/-- Complete analytic induction step, with the exact manuscript scale η. -/
theorem absorption_successor {K : ℕ → ℝ} (hK : WronskianExponents K)
    {m : ℕ} (hm : 1 ≤ m) {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (habs : AbsorptionAt m (disk r₀)) :
    AbsorptionAt (m + 1) (disk (eta K (m + 1) * r₀)) := by
  classical
  let η := eta K (m + 1)
  let δ := η * r₀
  have hm1 : 1 ≤ m + 1 := by omega
  have hmR : (0 : ℝ) < m + 1 := by positivity
  have hKm := (hK (m + 1) hm1).1
  have hη : 0 < η := eta_pos hm1 hKm
  have hη64 : η ≤ 1 / 64 := by
    change 1 / (1024 * (K (m + 1) + (m + 1 : ℕ))) ≤ 1 / 64
    have hmone : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast hm1
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1024 * (K (m + 1) + (m + 1 : ℕ)))).mpr
    nlinarith
  have hη1 : η < 1 := by linarith
  have hδ : 0 < δ := mul_pos hη hr₀
  have hδη : δ ≤ η := mul_le_of_le_one_right hη.le hr₀1
  have hδ1 : δ ≤ 1 := hδη.trans hη1.le
  intro A a s hA ha hsmall hsum hsne
  by_contra hn
  have hno : ∀ i, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence
      (fun n z => (A i (φ n) z)⁻¹) (fun _ => 0) (disk δ) := by
    intro i hi
    exact hn ⟨i, hi⟩
  obtain ⟨ell, hell, hgap⟩ := absorption_combination_gap habs hη hη1 A a s hA ha hsmall hsum hsne hno
  obtain ⟨F, hFδ, _hF, C₀, hC₀, hpoints⟩ := finite_unit_failure_points A isOpen_ball
    (fun i n z hz => (hA i n).2 z (ball_subset_ball hδ1 hz)) hno
  obtain ⟨α, β, c, ρ, hα, hαβ, hβ, _hc, hρ, hMlim, hgood⟩ :=
    absorption_growth_radii (by omega) hA ha hsmall hsum hsne
  let M := fun n => unitGrowthMean (fun i => A i n) (ρ n)
  let R := fun n => ρ n + 1 / M n
  have hM : Tendsto M atTop atTop := hMlim
  have hρ0 : ∀ n, 0 < ρ n := fun n => by linarith [(hρ n).1]
  have hρ1 : ∀ n, ρ n < 1 := fun n => by linarith [(hρ n).2]
  have hρhalf : ∀ n, 1 / 2 ≤ ρ n := fun n => hα.le.trans (hρ n).1
  obtain ⟨B, hB, hjet⟩ := compactConvergence_jet_bound isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
    (closedBall_subset_ball (by norm_num : (3 / 4 : ℝ) < 1))
    (isCompact_closedBall (0 : ℂ) (3 / 4)) (m + 1)
  let e := fun n => Real.circleAverage (wronskianBoundaryError (fun i => a i n) B) 0 (ρ n)
  let E := fun n => (m + 1 : ℕ) * C₀ + e n
  let I := fun n => Real.circleAverage (fun z => Real.log ‖wronskian (fun i => a i n) z‖) 0 (ρ n)
  have he0 : ∀ n, 0 ≤ e n := fun n => Real.circleAverage_nonneg_of_nonneg
    (fun z _ => wronskianBoundaryError_nonneg (fun i => a i n) hB z)
  have heE : ∀ n, e n ≤ E n := fun n => le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hC₀)
  have hcoords : ∀ᶠ n in atTop, ∀ i, ell ≤ diskSupNorm (a i n) η := by
    filter_upwards [hgap] with n hn i
    exact hn.trans (leastCombinationNorm_le_coordinate hη.le
      (fun i => (ha i n).continuousOn.mono (closedBall_subset_ball hη1)) i)
  have hderivdata : ∀ᶠ n in atTop, 1 / 2 ≤ ρ n ∧ ρ n < R n ∧ R n < 1 ∧
      R n - ρ n = 1 / M n ∧ ∀ i, ell ≤ diskSupNorm (a i n) η ∧ proximityMean (a i n) (R n) ≤ 2 * M n := by
    filter_upwards [hgood, hcoords] with n hgn hcn
    have hMn : 0 < M n := hgn.1
    have hRn : R n < β := hgn.2.1
    have hrR : ρ n < R n := lt_add_of_pos_right _ (one_div_pos.mpr hMn)
    have hR1 : R n < 1 := by linarith
    refine ⟨hρhalf n, hrR, hR1, by dsimp [R]; ring, ?_⟩
    intro i
    refine ⟨hcn i, ?_⟩
    apply le_trans _ hgn.2.2.1
    apply proximityMean_le_unitGrowthMean ((hρ0 n).trans hrR).le hR1 (fun i => hA i n)
      (((ha i n).analyticOnNhd isOpen_ball).mono (sphere_subset_ball hR1) |>.meromorphicOn) i
    intro z hz
    have hzR : ‖z‖ = R n := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hgn.2.2.2.2 i z (by rw [hzR]; linarith)
  have heLittle : e =o[atTop] M := wronskian_boundary_error_negligible hη (by linarith) hell
    a ρ R M B ha (fun n => ⟨(hρ0 n).le, hρ1 n⟩) hM hderivdata
  have hELittle : E =o[atTop] M := by
    exact ((isLittleO_const_id_atTop ((m + 1 : ℕ) * C₀)).comp_tendsto hM).add heLittle
  obtain ⟨D, hD, hWlower⟩ := absorption_wronskian_growth_lower (C₀ := C₀) hK hm1 hη (by linarith) hell
  have hcomparison : ∀ᶠ n in atTop,
      I n ≤ (8 * (m + 1 : ℕ) * δ - 1) * M n + E n ∧
      -(128 * K (m + 1) + 20 * (m + 1 : ℕ)) / (1024 * (K (m + 1) + (m + 1 : ℕ))) * M n -
        2 * D - E n ≤ I n := by
    filter_upwards [hgood, hgap, hcoords, hpoints] with n hgn hgapn hcn hpn
    have hMn : 0 ≤ M n := hgn.1.le
    have henv := absorption_envelope_bounds (hρhalf n) (hρ1 n) hδ hδη hη64 hC₀
      (fun i => hA i n)
      (fun i => (ha i n).continuousOn.mono (closedBall_subset_ball (by linarith : 4 * η < 1)))
      (fun i z hz => hgn.2.2.2.2 i z (by linarith))
      (fun i => by obtain ⟨z, hz, hzC⟩ := hpn i; exact ⟨z, hFδ hz, hzC⟩)
    have habound : ∀ i z, ‖z‖ ≤ 4 * η → ‖a i n z‖ ≤ Real.exp (64 * η * M n + C₀) := by
      intro i z hz
      have hzK : z ∈ closedBall (0 : ℂ) (4 * η) := by simpa using hz
      have hb := (isCompact_closedBall (0 : ℂ) (4 * η)).bddAbove_image
        ((ha i n).continuousOn.mono (closedBall_subset_ball (by linarith : 4 * η < 1))).norm
      exact (le_csSup hb (mem_image_of_mem (fun z => ‖a i n z‖) hzK)).trans (henv i).2
    obtain ⟨w, hw, hWnz, hwlower⟩ := hWlower (fun i => a i n) (M n) hMn (fun i => ha i n) habound hgapn
    have han : ∀ i, ∃ z ∈ disk 1, a i n z ≠ 0 := by
      intro i
      obtain ⟨z, hz, hmax⟩ := diskSupNorm_attained hη.le
        ((ha i n).continuousOn.mono (closedBall_subset_ball hη1))
      have hp : 0 < ‖a i n z‖ := by rw [← hmax]; exact hell.trans_le (hcn i)
      exact ⟨z, closedBall_subset_ball hη1 hz, norm_pos_iff.mp hp⟩
    have hwunit : w ∈ disk 1 := by
      have : ‖w‖ < 1 := by linarith
      simpa [disk] using this
    have hmeans := wronskian_boundary_mean_estimates hm1 (hρ0 n) (hρ1 n) hB (fun i => ha i n) (fun i => hA i n)
      han ⟨w, hwunit, hWnz⟩
      (fun i z hz => hgn.2.2.2.2 i z (by
        have hzρ : ‖z‖ = ρ n := by simpa only [mem_sphere, dist_zero_right] using hz
        rw [hzρ]; linarith [(hρ n).2]))
      (fun k z hz => hjet n k z (by
        have hzρ : ‖z‖ = ρ n := by simpa only [mem_sphere, dist_zero_right] using hz
        simp only [mem_closedBall, dist_zero_right, hzρ]
        linarith [(hρ n).2]))
      (fun z hz => by
        have hzρ : ‖z‖ = ρ n := by simpa only [mem_sphere, dist_zero_right] using hz
        exact (hgn.2.2.2.1 z (by rw [hzρ]; exact (hρ n).1) (by rw [hzρ]; exact (hρ n).2.le)).2)
    have hsumcenter : (∑ i, Real.log ‖A i n 0‖) ≤ (m + 1 : ℕ) * (8 * δ * M n + C₀) := by
      calc
        _ ≤ ∑ _i : Fin (m + 1), (8 * δ * M n + C₀) := Finset.sum_le_sum (fun i _ => (henv i).1)
        _ = _ := by simp; ring
    have hu : I n ≤ (8 * (m + 1 : ℕ) * δ - 1) * M n + E n := by
      have hh : I n ≤ (∑ i, Real.log ‖A i n 0‖) - M n + e n := hmeans.1
      dsimp [E]
      nlinarith only [hh, hsumcenter]
    have hWholo := (wronskian_analyticOnNhd (fun i => (ha i n).analyticOnNhd isOpen_ball)).mono
      (closedBall_subset_ball (hρ1 n))
    have hl := wronskian_mean_lower_from_point (hρhalf n) hη.le hη64 hMn hD (he0 n)
      ((Nat.cast_nonneg _).trans hKm) (by exact_mod_cast hm1) hWholo hw hWnz hwlower hmeans.2
    refine ⟨hu, ?_⟩
    have hh : -(128 * K (m + 1) + 20 * (m + 1 : ℕ)) * η * M n - 2 * D - e n ≤ I n := hl
    have heq : -(128 * K (m + 1) + 20 * (m + 1 : ℕ)) / (1024 * (K (m + 1) + (m + 1 : ℕ))) =
        -(128 * K (m + 1) + 20 * (m + 1 : ℕ)) * η := by dsimp [η, eta]; ring
    rw [heq]
    linarith [heE n]
  exact absorption_growth_contradiction (m := (m + 1 : ℕ)) (by positivity) hKm hδη hM hELittle
    (hcomparison.mono (fun n hn => hn.1)) (hcomparison.mono (fun n hn => hn.2))

end ModifiedCartan
