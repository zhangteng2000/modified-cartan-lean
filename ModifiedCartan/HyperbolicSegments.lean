import ModifiedCartan.HyperbolicRealSegment

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real
namespace ModifiedCartan

theorem diskSegmentMap_surjective_on {a ξ : ℂ} {t : ℝ}
    (ha : ‖a‖ < 1) (hξ : ‖ξ‖ = 1) (ht : |t| < 1) {z : ℂ} (hz : z ∈ disk 1) :
    ∃ w ∈ disk 1, diskSegmentMap a ξ t w = z := by
  have htn : ‖(t : ℂ)‖ < 1 := by simpa using ht
  have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hξ
  have hmid : ξ⁻¹ * diskAutomorphism a z ∈ disk 1 := by
    have hh := diskAutomorphism_mem_disk ha hz
    simpa only [disk, mem_ball, dist_zero_right, norm_mul, norm_inv, hξ, inv_one, one_mul] using hh
  refine ⟨-diskAutomorphism (t : ℂ) (ξ⁻¹ * diskAutomorphism a z), ?_, ?_⟩
  · simpa only [disk, mem_ball, dist_zero_right, norm_neg] using diskAutomorphism_mem_disk htn hmid
  · rw [diskSegmentMap, neg_neg, diskAutomorphism_involutive htn hmid,
      mul_inv_cancel_left₀ hξ0, diskAutomorphism_involutive ha hz]

/-- The actual distance-additive segment is exactly the image of the symmetric
real segment under the explicitly constructed disk automorphism. -/
theorem hyperbolicSegment_diskSegmentMap {a ξ : ℂ} {t : ℝ}
    (ha : ‖a‖ < 1) (hξ : ‖ξ‖ = 1) (ht0 : 0 ≤ t) (ht : |t| < 1) :
    hyperbolicSegment (diskSegmentMap a ξ t ((-t : ℝ) : ℂ)) (diskSegmentMap a ξ t (t : ℂ)) =
      (fun s : ℝ => diskSegmentMap a ξ t (s : ℂ)) '' Icc (-t) t := by
  have hlt : ((-t : ℝ) : ℂ) ∈ disk 1 := by simpa [disk] using ht
  have hrt : (t : ℂ) ∈ disk 1 := by simpa [disk] using ht
  have hneg : |-t| < 1 := by simpa using ht
  have hle : -t ≤ t := by linarith
  ext z
  constructor
  · rintro ⟨hz, he⟩
    obtain ⟨w, hw, rfl⟩ := diskSegmentMap_surjective_on ha hξ ht hz
    have hwseg : w ∈ hyperbolicSegment (((-t : ℝ) : ℂ)) (t : ℂ) := by
      refine ⟨hw, ?_⟩
      simpa only [diskSegmentMap_preserves_distance ha hξ ht hlt hw,
        diskSegmentMap_preserves_distance ha hξ ht hw hrt,
        diskSegmentMap_preserves_distance ha hξ ht hlt hrt] using he
    rw [hyperbolicSegment_real hneg ht hle] at hwseg
    obtain ⟨s, hs, rfl⟩ := hwseg
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    have hs1 : |s| < 1 := (abs_le.mpr hs).trans_lt (by simpa [abs_of_nonneg ht0] using ht)
    have hsD : (s : ℂ) ∈ disk 1 := by simpa [disk] using hs1
    refine ⟨diskSegmentMap_mem_disk ha hξ ht hsD, ?_⟩
    rw [diskSegmentMap_preserves_distance ha hξ ht hlt hsD,
      diskSegmentMap_preserves_distance ha hξ ht hsD hrt,
      diskSegmentMap_preserves_distance ha hξ ht hlt hrt]
    exact hyperbolicDistance_real_additive hneg hs1 ht hs.1 hs.2

end ModifiedCartan
