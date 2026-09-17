import ModifiedCartan.Harmonic

/-! The harmonic envelope estimate, with the constants of `lem:envelope`. -/
noncomputable section
open Complex InnerProductSpace Metric Real
namespace ModifiedCartan

theorem harnack_defect_bound {R r : ℝ} (hR : 1 / 2 ≤ R)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    1 - ((R - r) / (R + r)) ^ 2 ≤ 8 * r := by
  have hd : 0 < R + r := by linarith
  have hh0 : 0 ≤ (R - r) / (R + r) := div_nonneg (by linarith) hd.le
  have hh1 : (R - r) / (R + r) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hid : 1 - (R - r) / (R + r) = 2 * r / (R + r) := by field_simp; ring
  have hb : 2 * r / (R + r) ≤ 4 * r := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hr (show 0 ≤ R - 1 / 2 by linarith), sq_nonneg r]
  nlinarith [sq_nonneg (1 - (R - r) / (R + r))]

/-- The coefficient estimate used in the second envelope inequality. -/
theorem envelope_coefficient_bound {R δ η : ℝ}
    (hR : 1 / 2 ≤ R) (hδ : 0 < δ) (hδη : δ ≤ η) (hη : η ≤ 1 / 64) :
    (R + 4 * η) / (R - 4 * η) -
      (R - 4 * η) / (R + 4 * η) * ((R - δ) / (R + δ)) ^ 2 ≤ 64 * η := by
  have hη0 : 0 ≤ η := le_trans hδ.le hδη
  have hδR : δ ≤ R := by linarith
  have h4R : 4 * η < R := by linarith
  have hd : 0 < R + 4 * η := by linarith
  let k := (R - 4 * η) / (R + 4 * η)
  let h := (R - δ) / (R + δ)
  let q := (R + 4 * η) / (R - 4 * η)
  have hk0 : 0 ≤ k := div_nonneg (by linarith) hd.le
  have hk1 : k ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hk : 2 / 3 ≤ k := by
    apply (le_div_iff₀ hd).mpr
    linarith
  have hqk : q * k = 1 := by
    dsimp [q, k]
    field_simp [ne_of_gt (sub_pos.mpr h4R)]
  have hdk : 1 - k ^ 2 ≤ 32 * η := by
    have hb := harnack_defect_bound hR (show 0 ≤ 4 * η by positivity) h4R.le
    change 1 - k ^ 2 ≤ 8 * (4 * η) at hb
    linarith
  have hdh : 1 - h ^ 2 ≤ 8 * η :=
    (harnack_defect_bound hR hδ.le hδR).trans (by gcongr)
  have hdiff0 : 0 ≤ q - k := by nlinarith
  have hdiff : q - k ≤ 48 * η := by nlinarith
  have hrest : k * (1 - h ^ 2) ≤ 8 * η := by
    have hh1 : h ≤ 1 := (div_le_one (by linarith : 0 < R + δ)).mpr (by linarith)
    have hh0 : 0 ≤ h := div_nonneg (by linarith) (by linarith)
    have hh : 0 ≤ 1 - h ^ 2 := by nlinarith
    exact (mul_le_of_le_one_left hh hk1).trans hdh
  change q - k * h ^ 2 ≤ 64 * η
  nlinarith

/-- Pointwise form of the envelope lemma. The boundary conditions express exactly
that U is the harmonic extension of the positive maximum of the uᵢ. -/
theorem envelope_pointwise {m : ℕ} {u : Fin m → ℂ → ℝ} {U : ℂ → ℝ}
    {ρ δ η C₀ : ℝ} (hρ : 1 / 2 ≤ ρ) (_hρ' : ρ ≤ 3 / 4)
    (hδ : 0 < δ) (hδη : δ ≤ η) (hη : η ≤ 1 / 64) (hC : 0 ≤ C₀)
    (hu : ∀ i, HarmonicOnNhd (u i) (closedBall 0 ρ))
    (hU : HarmonicContOnCl U (ball 0 ρ))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) ρ,
      IsGreatest (Set.range (fun i => u i z)) (U z) ∧ 0 < U z)
    (hpoints : ∀ i, ∃ z ∈ ball (0 : ℂ) δ, u i z ≤ C₀) :
    ∀ i, u i 0 ≤ 8 * δ * U 0 + C₀ ∧
      ∀ z : ℂ, ‖z‖ ≤ 4 * η → u i z ≤ 64 * η * U 0 + C₀ := by
  have hρ0 : 0 < ρ := by linarith
  have hδρ : δ < ρ := by linarith
  have h4ρ : 4 * η < ρ := by linarith
  have hη0 : 0 ≤ η := hδ.le.trans hδη
  have hUb : ∀ z ∈ sphere (0 : ℂ) ρ, 0 ≤ U z := fun z hz => (hboundary z hz).2.le
  have hM : 0 ≤ U 0 := harmonic_nonneg_of_boundary hU hUb (mem_ball_self hρ0)
  intro i
  have hui : HarmonicContOnCl (u i) (ball 0 ρ) := by
    apply HarmonicOnNhd.harmonicContOnCl
    simpa [closure_ball (0 : ℂ) hρ0.ne'] using hu i
  have hV := hU.sub hui
  have hVb : ∀ z ∈ sphere (0 : ℂ) ρ, 0 ≤ (U - u i) z := by
    intro z hz
    exact sub_nonneg.mpr ((hboundary z hz).1.2 (Set.mem_range_self i))
  obtain ⟨w, hw, hwi⟩ := hpoints i
  have hwn : ‖w - 0‖ ≤ δ := (mem_ball_iff_norm.mp hw).le
  let h := (ρ - δ) / (ρ + δ)
  have hh0 : 0 ≤ h := div_nonneg (by linarith) (by linarith)
  have hh1 : h ≤ 1 := (div_le_one (by linarith : 0 < ρ + δ)).mpr (by linarith)
  have hUw := (harmonic_harnack_uniform hU hUb hδ.le hδρ hwn).1
  have hVw := (harmonic_harnack_uniform hV hVb hδ.le hδρ hwn).2
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
    have hzn : ‖z - 0‖ ≤ 4 * η := by simpa using hz
    have hUz := (harmonic_harnack_uniform hU hUb (by positivity) h4ρ hzn).2
    have hVz := (harmonic_harnack_uniform hV hVb (by positivity) h4ρ hzn).1
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

/-- `lem:envelope`, including the actual supremum on the closed inner disk. -/
theorem envelope_lemma {m : ℕ} {u : Fin m → ℂ → ℝ} {U : ℂ → ℝ}
    {ρ δ η C₀ : ℝ} (hρ : 1 / 2 ≤ ρ) (hρ' : ρ ≤ 3 / 4)
    (hδ : 0 < δ) (hδη : δ ≤ η) (hη : η ≤ 1 / 64) (hC : 0 ≤ C₀)
    (hu : ∀ i, HarmonicOnNhd (u i) (closedBall 0 ρ))
    (hU : HarmonicContOnCl U (ball 0 ρ))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) ρ,
      IsGreatest (Set.range (fun i => u i z)) (U z) ∧ 0 < U z)
    (hpoints : ∀ i, ∃ z ∈ ball (0 : ℂ) δ, u i z ≤ C₀) :
    ∀ i, u i 0 ≤ 8 * δ * U 0 + C₀ ∧
      sSup (u i '' closedBall (0 : ℂ) (4 * η)) ≤ 64 * η * U 0 + C₀ := by
  intro i
  obtain ⟨h0, hinner⟩ := envelope_pointwise hρ hρ' hδ hδη hη hC hu hU hboundary hpoints i
  refine ⟨h0, csSup_le ?_ ?_⟩
  · exact (nonempty_closedBall.mpr (by linarith : 0 ≤ 4 * η)).image (u i)
  · rintro _ ⟨z, hz, rfl⟩
    exact hinner z (by simpa using hz)

end ModifiedCartan
