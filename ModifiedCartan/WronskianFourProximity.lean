import ModifiedCartan.WronskianQuotients

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

theorem normalizedWronskian_four_factor {g : Fin 4 → ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, g j z ≠ 0) (h012 : wronskian ![g 0,g 1,g 2] z ≠ 0)
    (h013 : wronskian ![g 0,g 1,g 3] z ≠ 0) :
    normalizedWronskian ![g 0,g 1] z * normalizedWronskian g z /
      (normalizedWronskian ![g 0,g 1,g 2] z * normalizedWronskian ![g 0,g 1,g 3] z) =
      wronskian ![g 0,g 1] z * wronskian g z /
      (wronskian ![g 0,g 1,g 2] z * wronskian ![g 0,g 1,g 3] z) := by
  simp [normalizedWronskian,Fin.prod_univ_four,Fin.prod_univ_three,Fin.prod_univ_two]
  field_simp [hg 0,hg 1,hg 2,hg 3]

/-- Exact proximity comparison in the four-term derived-fraction branch.
The choice of side is allowed to depend on the radius. -/
theorem wronskian_four_circle_proximity_alternative {g : Fin 4 → ℂ → ℂ} {R C : ℝ}
    (hR : 0 < R) (hR1 : R < 1) (hC : 0 ≤ C)
    (hg : ∀ j, IsHolomorphicUnit (g j) (disk 1))
    (h012 : ∀ z ∈ sphere (0 : ℂ) R, wronskian ![g 0,g 1,g 2] z ≠ 0)
    (h013 : ∀ z ∈ sphere (0 : ℂ) R, wronskian ![g 0,g 1,g 3] z ≠ 0)
    (hD : ∀ z ∈ sphere (0 : ℂ) R,
      ‖wronskian ![g 0,g 1] z * wronskian g z / (wronskian ![g 0,g 1,g 2] z * wronskian ![g 0,g 1,g 3] z)‖ ≤ C) :
    (proximityMean (fun z => g 2 z/g 3 z) R ≤ 2*Real.pi*R*C +
      proximityMean (normalizedWronskian ![g 0,g 1,g 3]) R +
      proximityMean (fun z => (normalizedWronskian ![g 0,g 1,g 2] z)⁻¹) R) ∨
    (proximityMean (fun z => g 3 z/g 2 z) R ≤ 2*Real.pi*R*C +
      proximityMean (normalizedWronskian ![g 0,g 1,g 2]) R +
      proximityMean (fun z => (normalizedWronskian ![g 0,g 1,g 3] z)⁻¹) R) := by
  let A := wronskian ![g 0,g 1,g 2]
  let B := wronskian ![g 0,g 1,g 3]
  let H := normalizedWronskian ![g 0,g 1,g 2]
  let K := normalizedWronskian ![g 0,g 1,g 3]
  have han : ∀ j, AnalyticOnNhd ℂ (g j) (disk 1) := fun j => (hg j).1.analyticOnNhd isOpen_ball
  have hA : AnalyticOnNhd ℂ A (disk 1) :=
    wronskian_analyticOnNhd (by intro j; fin_cases j <;> simpa using han _)
  have hB : AnalyticOnNhd ℂ B (disk 1) :=
    wronskian_analyticOnNhd (by intro j; fin_cases j <;> simpa using han _)
  have hH : AnalyticOnNhd ℂ H (disk 1) := normalizedWronskian_analyticOnNhd
    (by intro j; fin_cases j <;> simpa using han _)
    (by intro j; fin_cases j <;> simpa using (hg _).2)
  have hK : AnalyticOnNhd ℂ K (disk 1) := normalizedWronskian_analyticOnNhd
    (by intro j; fin_cases j <;> simpa using han _)
    (by intro j; fin_cases j <;> simpa using (hg _).2)
  have hsub : sphere (0 : ℂ) |R| ⊆ disk 1 := by
    rw [abs_of_pos hR]
    exact sphere_subset_ball hR1
  have hAm := (hA.mono hsub).meromorphicOn
  have hBm := (hB.mono hsub).meromorphicOn
  have hHm := (hH.mono hsub).meromorphicOn
  have hKm := (hK.mono hsub).meromorphicOn
  have hc := circle_logDerivative_proximity_alternative hR hC (hAm.div hBm)
    (fun z hz => (hA z (sphere_subset_ball hR1 hz)).differentiableAt.div
      (hB z (sphere_subset_ball hR1 hz)).differentiableAt (h013 z hz))
    (fun z hz => div_ne_zero (h012 z hz) (h013 z hz))
    (fun z hz => ?_)
  · have hfor : EqOn (fun z => g 2 z/g 3 z)
        (fun z => (A z/B z)*(K z/H z)) (sphere (0 : ℂ) |R|) := by
      intro z hz
      have hz' : z ∈ sphere (0 : ℂ) R := by simpa only [abs_of_pos hR] using hz
      exact unit_quotient_three_wronskian_factor (fun j => (hg j).2 z (hsub hz)) (h012 z hz') (h013 z hz')
    have hrev : EqOn (fun z => g 3 z/g 2 z)
        (fun z => (A z/B z)⁻¹*(H z/K z)) (sphere (0 : ℂ) |R|) := by
      intro z hz
      have hh := congrArg (fun q : ℂ => q⁻¹) (hfor hz)
      simpa only [inv_div,mul_inv] using hh
    rcases hc with hc | hc
    · left
      rw [proximityMean_congr_circle hfor]
      have hp := (proximityMean_mul_le (hAm.div hBm) (hKm.div hHm)).trans
        (add_le_add hc (proximityMean_div_le hKm hHm))
      simpa only [Pi.div_def,Pi.inv_def,add_assoc] using hp
    · right
      rw [proximityMean_congr_circle hrev]
      have hp := (proximityMean_mul_le (hAm.div hBm).inv (hHm.div hKm)).trans
        (add_le_add hc (proximityMean_div_le hHm hKm))
      simpa only [Pi.div_def,Pi.inv_def,add_assoc] using hp
  · change ‖logDeriv (fun w => wronskian ![g 0,g 1,g 2] w / wronskian ![g 0,g 1,g 3] w) z‖ ≤ C
    rw [logDeriv_wronskian_ratio_four
      (fun j => (han j z (sphere_subset_ball hR1 hz)).differentiableAt)
      (fun j => ((han j).deriv z (sphere_subset_ball hR1 hz)).differentiableAt)
      (fun j => ((han j).deriv.deriv z (sphere_subset_ball hR1 hz)).differentiableAt) (h012 z hz) (h013 z hz)]
    simpa only [neg_div,norm_neg] using hD z hz

end ModifiedCartan
