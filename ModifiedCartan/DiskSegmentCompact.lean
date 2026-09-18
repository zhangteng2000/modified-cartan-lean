import ModifiedCartan.SymmetricDiskSegments

noncomputable section
set_option autoImplicit false
open Filter Topology Complex Metric Set
namespace ModifiedCartan

theorem diskAutomorphism_continuousAt_pair {a z : ℂ} (ha : a ∈ disk 1) (hz : z ∈ disk 1) :
    ContinuousAt (fun p : ℂ × ℂ => diskAutomorphism p.1 p.2) (a, z) :=
  diskAutomorphism_joint_continuous.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ha, hz⟩)

theorem diskSegmentMap_joint_continuousAt {a ξ z : ℂ} {t : ℝ}
    (ha : ‖a‖ < 1) (hξ : ‖ξ‖ = 1) (ht : |t| < 1) (hz : z ∈ disk 1) :
    ContinuousAt (fun p : ℂ × ℂ × ℝ × ℂ => diskSegmentMap p.1 p.2.1 p.2.2.1 p.2.2.2) (a, ξ, t, z) := by
  have ht' : (t : ℂ) ∈ disk 1 := by simpa [disk] using ht
  have hz' : -z ∈ disk 1 := by simpa [disk] using hz
  have hinner : ContinuousAt (fun p : ℂ × ℂ × ℝ × ℂ =>
      diskAutomorphism (p.2.2.1 : ℂ) (-p.2.2.2)) (a, ξ, t, z) := by
    apply ContinuousAt.comp (f := fun p : ℂ × ℂ × ℝ × ℂ => ((p.2.2.1 : ℂ), -p.2.2.2))
      (g := fun p : ℂ × ℂ => diskAutomorphism p.1 p.2) (diskAutomorphism_continuousAt_pair ht' hz')
    exact ((Complex.continuous_ofReal.comp (by fun_prop)).prodMk (by fun_prop)).continuousAt
  have hprod : ξ * diskAutomorphism (t : ℂ) (-z) ∈ disk 1 := by
    have hi := diskAutomorphism_mem_disk (a := (t : ℂ)) (by simpa using ht) hz'
    simpa only [disk, mem_ball, dist_zero_right, norm_mul, hξ, one_mul] using hi
  apply ContinuousAt.comp (f := fun p : ℂ × ℂ × ℝ × ℂ =>
      (p.1, p.2.1 * diskAutomorphism (p.2.2.1 : ℂ) (-p.2.2.2)))
    (g := fun p : ℂ × ℂ => diskAutomorphism p.1 p.2)
    (diskAutomorphism_continuousAt_pair (by simpa [disk] using ha) hprod)
  exact continuousAt_fst.prodMk ((by fun_prop : ContinuousAt (fun p : ℂ × ℂ × ℝ × ℂ => p.2.1) (a, ξ, t, z)).mul hinner)

/-- A compact family of normalized disk-segment maps sends every fixed compact
subdisk into one strictly smaller subdisk, uniformly in all parameters. -/
theorem diskSegmentMap_uniform_norm {d q v : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hq : 0 ≤ q) (hq1 : q < 1) (hv : 0 ≤ v) (hv1 : v < 1) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∀ (a ξ z : ℂ) (t : ℝ),
      ‖a‖ ≤ d → ‖ξ‖ = 1 → 0 ≤ t → t ≤ q → ‖z‖ ≤ v →
      ‖diskSegmentMap a ξ t z‖ ≤ p := by
  let K : Set (ℂ × ℂ × ℝ × ℂ) := closedBall 0 d ×ˢ sphere 0 1 ×ˢ Icc 0 q ×ˢ closedBall 0 v
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) d).prod
    ((isCompact_sphere (0 : ℂ) 1).prod (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) v)))
  have hKne : K.Nonempty := ⟨(0, 1, 0, 0), by simp [K, hd, hq, hv]⟩
  have hpoint : ∀ p ∈ K,
      ContinuousAt (fun p : ℂ × ℂ × ℝ × ℂ => diskSegmentMap p.1 p.2.1 p.2.2.1 p.2.2.2) p ∧
      ‖diskSegmentMap p.1 p.2.1 p.2.2.1 p.2.2.2‖ < 1 := by
    intro p hp
    have ha : ‖p.1‖ < 1 := (show ‖p.1‖ ≤ d by simpa only [mem_closedBall, dist_zero_right] using hp.1).trans_lt hd1
    have hξ : ‖p.2.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp.2.1
    have ht : |p.2.2.1| < 1 := by rw [abs_of_nonneg hp.2.2.1.1]; exact hp.2.2.1.2.trans_lt hq1
    have hz : p.2.2.2 ∈ disk 1 := closedBall_subset_ball hv1 hp.2.2.2
    exact ⟨diskSegmentMap_joint_continuousAt ha hξ ht hz, by simpa [disk] using diskSegmentMap_mem_disk ha hξ ht hz⟩
  obtain ⟨p₀, hp₀, hmax⟩ := hK.exists_isMaxOn hKne
    (fun p hp => (hpoint p hp).1.norm.continuousWithinAt)
  let M := ‖diskSegmentMap p₀.1 p₀.2.1 p₀.2.2.1 p₀.2.2.2‖
  have hM : M < 1 := (hpoint p₀ hp₀).2
  have hM0 : 0 ≤ M := norm_nonneg _
  refine ⟨(M + 1) / 2, by linarith, by linarith, ?_⟩
  intro a ξ z t ha hξ ht htq hz
  have hp : (a, ξ, t, z) ∈ K := by
    exact ⟨by simpa using ha, by simpa using hξ, ⟨ht, htq⟩, by simpa using hz⟩
  have hle := hmax hp
  exact hle.trans (by dsimp [M]; linarith)

end ModifiedCartan
