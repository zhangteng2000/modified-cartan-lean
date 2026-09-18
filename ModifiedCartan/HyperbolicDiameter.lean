import ModifiedCartan.DiskAutomorphisms

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Complex Metric Set Real
namespace ModifiedCartan

theorem diskAutomorphism_joint_continuous :
    ContinuousOn (fun p : ℂ × ℂ => diskAutomorphism p.1 p.2) (disk 1 ×ˢ disk 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro p hp
  exact diskAutomorphism_denominator_ne_zero (by simpa [disk] using hp.1)
    (le_of_lt (by simpa [disk] using hp.2))

theorem diskAutomorphism_image_open {a : ℂ} (ha : ‖a‖ < 1) {U : Set ℂ}
    (hU : IsOpen U) (hU1 : U ⊆ disk 1) : IsOpen (diskAutomorphism a '' U) := by
  have he : diskAutomorphism a '' U = disk 1 ∩ diskAutomorphism a ⁻¹' U := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨diskAutomorphism_mem_disk ha (hU1 hw), by
        simpa only [mem_preimage, diskAutomorphism_involutive ha (hU1 hw)] using hw⟩
    · rintro ⟨hz, hw⟩
      exact ⟨diskAutomorphism a z, hw, diskAutomorphism_involutive ha hz⟩
  rw [he]
  exact ((diskAutomorphism_analytic ha).continuousOn.mono ball_subset_closedBall).isOpen_inter_preimage
    isOpen_ball hU

theorem hyperbolicDistance_le_log_three_iff {z w : ℂ} (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    hyperbolicDistance z w ≤ Real.log 3 ↔ ‖diskAutomorphism w z‖ ≤ 1 / 2 := by
  have hn : ‖diskAutomorphism w z‖ < 1 := by
    simpa [disk] using diskAutomorphism_mem_disk (show ‖w‖ < 1 by simpa [disk] using hw) hz
  have hden : 0 < 1 - ‖diskAutomorphism w z‖ := by linarith
  rw [hyperbolicDistance_eq_automorphism,
    Real.log_le_log_iff (div_pos (by positivity) hden) (by norm_num), div_le_iff₀ hden]
  constructor <;> intro h <;> linarith

/-- An open set satisfying the manuscript's non-strict diameter endpoint has a
strict bound for every pair of its points. Connectedness is not used. -/
theorem open_diameter_strict_pseudodistance {U : Set ℂ} (hU : IsOpen U) (hU1 : U ⊆ disk 1)
    (hdiam : HasHyperbolicDiameterLE U (Real.log 3)) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    ‖diskAutomorphism w z‖ < 1 / 2 := by
  have hwn : ‖w‖ < 1 := by simpa [disk] using hU1 hw
  have himage := diskAutomorphism_image_open hwn hU hU1
  have hbound : diskAutomorphism w '' U ⊆ closedBall (0 : ℂ) (1 / 2) := by
    rintro x ⟨t, ht, rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using
      (hyperbolicDistance_le_log_three_iff (hU1 ht) (hU1 hw)).mp (hdiam t ht w hw)
  have hinterior := interior_maximal hbound himage
  rw [interior_closedBall _ (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hinterior
  simpa only [mem_ball, dist_zero_right] using hinterior (mem_image_of_mem _ hz)

theorem compact_strict_pseudodiameter {U K : Set ℂ} (hU : IsOpen U) (hU1 : U ⊆ disk 1)
    (hdiam : HasHyperbolicDiameterLE U (Real.log 3)) (hK : IsCompact K) (hne : K.Nonempty)
    (hKU : K ⊆ U) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 / 2 ∧ ∀ z ∈ K, ∀ w ∈ K, ‖diskAutomorphism w z‖ ≤ q := by
  have hc : ContinuousOn (fun p : ℂ × ℂ => ‖diskAutomorphism p.1 p.2‖) (K ×ˢ K) :=
    diskAutomorphism_joint_continuous.norm.mono (prod_mono (hKU.trans hU1) (hKU.trans hU1))
  obtain ⟨p, hp, hmax⟩ := (hK.prod hK).exists_isMaxOn (hne.prod hne) hc
  refine ⟨‖diskAutomorphism p.1 p.2‖, norm_nonneg _,
    open_diameter_strict_pseudodistance hU hU1 hdiam (hKU hp.2) (hKU hp.1), ?_⟩
  intro z hz w hw
  exact hmax (show (w, z) ∈ K ×ˢ K from ⟨hw, hz⟩)

end ModifiedCartan
