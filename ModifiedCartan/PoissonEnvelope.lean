import ModifiedCartan.PoissonHarnack
import ModifiedCartan.Envelope

noncomputable section
set_option autoImplicit false
open Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

/-- The exact envelope constants obtained from a constructed Poisson extension,
without an additional envelope-existence hypothesis. -/
theorem poisson_envelope_pointwise {m : ℕ} {u : Fin m → ℂ → ℝ} {v : ℂ → ℝ}
    {ρ δ η C₀ : ℝ} (hρ : 1 / 2 ≤ ρ)
    (hδ : 0 < δ) (hδη : δ ≤ η) (hη : η ≤ 1 / 64) (hC : 0 ≤ C₀)
    (hu : ∀ i, HarmonicOnNhd (u i) (closedBall 0 ρ))
    (hv : CircleIntegrable v 0 ρ) (hv0 : ∀ ζ ∈ sphere (0 : ℂ) |ρ|, 0 ≤ v ζ)
    (hdom : ∀ i ζ, ζ ∈ sphere (0 : ℂ) |ρ| → u i ζ ≤ v ζ)
    (hpoints : ∀ i, ∃ z ∈ ball (0 : ℂ) δ, u i z ≤ C₀) :
    ∀ i, u i 0 ≤ 8 * δ * Real.circleAverage v 0 ρ + C₀ ∧
      ∀ z : ℂ, ‖z‖ ≤ 4 * η → u i z ≤ 64 * η * Real.circleAverage v 0 ρ + C₀ := by
  have hρ0 : 0 < ρ := by linarith
  have hδρ : δ < ρ := by linarith
  have h4ρ : 4 * η < ρ := by linarith
  have hη0 : 0 ≤ η := hδ.le.trans hδη
  let U := poissonExtension v ρ
  have hU0 : U 0 = Real.circleAverage v 0 ρ := poissonExtension_zero hρ0 hv
  have hM : 0 ≤ U 0 := poissonExtension_nonneg hv hv0 (mem_ball_self hρ0)
  rw [← hU0]
  intro i
  have hui : HarmonicContOnCl (u i) (ball 0 ρ) := by
    apply HarmonicOnNhd.harmonicContOnCl
    simpa [closure_ball (0 : ℂ) hρ0.ne'] using hu i
  have huiInt : CircleIntegrable (u i) 0 ρ := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hρ0]
    exact (hu i).continuousOn.mono sphere_subset_closedBall
  have hvi : CircleIntegrable (fun z => v z - u i z) 0 ρ := by
    simpa only [Pi.sub_def] using hv.sub huiInt
  have hvi0 : ∀ ζ ∈ sphere (0 : ℂ) |ρ|, 0 ≤ v ζ - u i ζ :=
    fun ζ hζ => sub_nonneg.mpr (hdom i ζ hζ)
  have hVeq : ∀ x ∈ ball (0 : ℂ) ρ,
      poissonExtension (fun ζ => v ζ - u i ζ) ρ x = U x - u i x := by
    intro x hx
    rw [poissonExtension_sub hv huiInt hx, poissonExtension_eq_harmonic hui hx]
  obtain ⟨w, hw, hwi⟩ := hpoints i
  have hwn : ‖w‖ ≤ δ := by simpa using (mem_ball_iff_norm.mp hw).le
  let h := (ρ - δ) / (ρ + δ)
  have hh0 : 0 ≤ h := div_nonneg (by linarith) (by linarith)
  have hh1 : h ≤ 1 := (div_le_one (by linarith : 0 < ρ + δ)).mpr (by linarith)
  have hUw := (poissonExtension_harnack_uniform hv hv0 hδ.le hδρ hwn).1
  have hVw := (poissonExtension_harnack_uniform hvi hvi0 hδ.le hδρ hwn).2
  rw [hVeq w (ball_subset_ball hδρ.le hw), hVeq 0 (mem_ball_self hρ0)] at hVw
  change h * U 0 ≤ U w at hUw
  change h * (U w - u i w) ≤ U 0 - u i 0 at hVw
  have hbase : h ^ 2 * U 0 - C₀ ≤ U 0 - u i 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hUw hh0,
      mul_le_mul_of_nonneg_left hwi hh0, mul_le_of_le_one_left hC hh1]
  constructor
  · have hd := harnack_defect_bound hρ hδ.le hδρ.le
    change 1 - h ^ 2 ≤ 8 * δ at hd
    nlinarith [mul_le_mul_of_nonneg_right hd hM]
  · intro z hz
    let k := (ρ - 4 * η) / (ρ + 4 * η)
    let q := (ρ + 4 * η) / (ρ - 4 * η)
    have hk0 : 0 ≤ k := div_nonneg (by linarith) (by linarith)
    have hk1 : k ≤ 1 := (div_le_one (by linarith : 0 < ρ + 4 * η)).mpr (by linarith)
    have hqk : q * k = 1 := by
      dsimp [q, k]
      field_simp [ne_of_gt (sub_pos.mpr h4ρ)]
    have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
    have hUz := (poissonExtension_harnack_uniform hv hv0 (by positivity) h4ρ hz).2
    have hVz := (poissonExtension_harnack_uniform hvi hvi0 (by positivity) h4ρ hz).1
    rw [hVeq 0 (mem_ball_self hρ0), hVeq z (by simpa using hz.trans_lt h4ρ)] at hVz
    change k * U z ≤ U 0 at hUz
    change k * (U 0 - u i 0) ≤ U z - u i z at hVz
    have hUq : U z ≤ q * U 0 := by
      have hm := mul_le_mul_of_nonneg_left hUz hq0
      rwa [← mul_assoc, hqk, one_mul] at hm
    have hi : u i z ≤ (q - k * h ^ 2) * U 0 + C₀ := by
      nlinarith [mul_le_mul_of_nonneg_left hbase hk0, mul_le_of_le_one_left hC hk1]
    have hc := envelope_coefficient_bound hρ hδ hδη hη
    change q - k * h ^ 2 ≤ 64 * η at hc
    exact hi.trans (by gcongr)

end ModifiedCartan
