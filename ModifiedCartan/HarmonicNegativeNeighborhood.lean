import ModifiedCartan.HarmonicComposition

noncomputable section
set_option autoImplicit false
open Filter Topology Complex InnerProductSpace Metric Set Real
namespace ModifiedCartan

theorem harnack_negative_coefficient {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ d : ℝ, 0 ≤ d → d ≤ δ →
      (R + d) / (R - d) - (R - d) / (R + d) * (1 + ε) ≤ -ε / 2 := by
  let f := fun d : ℝ => (R + d) / (R - d) - (R - d) / (R + d) * (1 + ε)
  have hc : ContinuousAt f 0 := by
    apply ContinuousAt.sub
    · exact (continuousAt_const.add continuousAt_id).div
        (continuousAt_const.sub continuousAt_id) (by simpa using hR.ne')
    · apply ContinuousAt.mul _ continuousAt_const
      exact (continuousAt_const.sub continuousAt_id).div
        (continuousAt_const.add continuousAt_id) (by simpa using hR.ne')
  have hf0 : f 0 < -ε / 2 := by simp only [f, add_zero, sub_zero, div_self hR.ne']; linarith
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hc.eventually (gt_mem_nhds hf0))
  refine ⟨min (R / 2) (r / 2), lt_min (half_pos hR) (half_pos hr),
    (min_le_left _ _).trans_lt (half_lt_self hR), ?_⟩
  intro d hd hdδ
  have hdr : d < r := (hdδ.trans (min_le_right _ _)).trans_lt (half_lt_self hr)
  exact (hsub (by simpa [Real.dist_eq, abs_of_nonneg hd] using hdr)).le

/-- A negative difference of two positive harmonic functions remains negative
on a disk of fixed width, uniformly in the functions and the center. -/
theorem harmonic_negative_neighborhood {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ (U V : ℂ → ℝ) (c : ℂ) (C : ℝ),
      HarmonicOnNhd U (ball c R) → HarmonicOnNhd V (ball c R) →
      (∀ z ∈ ball c R, 0 ≤ U z) → (∀ z ∈ ball c R, 0 ≤ V z) →
      0 ≤ C → U c - V c ≤ -ε * U c + C →
      ∀ z : ℂ, ‖z - c‖ ≤ δ → U z - V z ≤ -(ε / 2) * U c + C := by
  obtain ⟨δ, hδ, hδR, hcoeff⟩ := harnack_negative_coefficient hR hε
  refine ⟨δ, hδ, hδR, ?_⟩
  intro U V c C hU hV hUpos hVpos hC hnegative z hz
  have hzR : z ∈ ball c R := mem_ball_iff_norm.mpr (hz.trans_lt hδR)
  have hUc := hUpos c (mem_ball_self hR)
  have hUpper := (harmonic_harnack_open hU hUpos hzR).2
  have hLower := (harmonic_harnack_open hV hVpos hzR).1
  let k := (R - ‖z - c‖) / (R + ‖z - c‖)
  have hk0 : 0 ≤ k := div_nonneg (by linarith) (by positivity)
  have hk1 : k ≤ 1 := (div_le_one (by positivity : 0 < R + ‖z - c‖)).mpr (by linarith [norm_nonneg (z - c)])
  have hVc : (1 + ε) * U c - C ≤ V c := by linarith
  have hVm := mul_le_mul_of_nonneg_left hVc hk0
  have hCm := mul_le_mul_of_nonneg_right hk1 hC
  have hFm := mul_le_mul_of_nonneg_right (hcoeff ‖z - c‖ (norm_nonneg _) hz) hUc
  dsimp [k] at hVm hCm
  nlinarith

theorem harmonic_negative_neighborhood_unit {r ε : ℝ} (hr1 : r < 1) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 - r ∧ ∀ (U V : ℂ → ℝ) (C : ℝ),
      HarmonicOnNhd U (disk 1) → HarmonicOnNhd V (disk 1) →
      (∀ z ∈ disk 1, 0 ≤ U z) → (∀ z ∈ disk 1, 0 ≤ V z) → 0 ≤ C →
      ∀ w : ℂ, ‖w‖ ≤ r → U w - V w ≤ -ε * U w + C →
      ∀ z : ℂ, ‖z - w‖ ≤ δ → z ∈ disk 1 ∧ U z - V z ≤ -(ε / 2) * U w + C := by
  obtain ⟨δ, hδ, hδR, hbound⟩ := harmonic_negative_neighborhood (sub_pos.mpr hr1) hε
  refine ⟨δ, hδ, hδR, ?_⟩
  intro U V C hU hV hUpos hVpos hC w hw hnegative z hz
  have hsub : ball w (1 - r) ⊆ disk 1 := by
    intro x hx
    have hxn : ‖x - w‖ < 1 - r := mem_ball_iff_norm.mp hx
    have ht : ‖x‖ ≤ ‖x - w‖ + ‖w‖ := by simpa only [sub_add_cancel] using norm_add_le (x - w) w
    simp only [disk, mem_ball, dist_zero_right]
    linarith
  exact ⟨hsub (mem_ball_iff_norm.mpr (hz.trans_lt hδR)),
    hbound U V w C (hU.mono hsub) (hV.mono hsub)
      (fun x hx => hUpos x (hsub hx)) (fun x hx => hVpos x (hsub hx)) hC hnegative z hz⟩

end ModifiedCartan
