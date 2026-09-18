import ModifiedCartan.SymmetricDiskSegments

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem compact_subset_unit_closedDisk {K : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) (hK1 : K ⊆ disk 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ K ⊆ closedBall 0 r := by
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have hzn : ‖z‖ < 1 := by simpa [disk] using hK1 hz
  refine ⟨(‖z‖ + 1) / 2, by positivity, by linarith, ?_⟩
  intro w hw
  have hle : ‖w‖ ≤ ‖z‖ := hmax hw
  simp only [mem_closedBall, dist_zero_right]
  linarith

/-- The strict pseudodiameter of a compact set persists uniformly when the
ambient disk is shrunk slightly. The manuscript endpoint remains non-strict. -/
theorem compact_scaled_pseudodiameter {U K : Set ℂ} (hU : IsOpen U)
    (hU1 : U ⊆ disk 1) (hdiam : HasHyperbolicDiameterLE U (Real.log 3))
    (hK : IsCompact K) (hne : K.Nonempty) (hKU : K ⊆ U) :
    ∃ q ρ₀ : ℝ, 0 < q ∧ q < sharpRadius ∧ 0 < ρ₀ ∧ ρ₀ < 1 ∧
      ∀ ρ ∈ Icc ρ₀ 1, ∀ a ∈ K, ∀ b ∈ K,
        a / (ρ : ℂ) ∈ disk 1 ∧ b / (ρ : ℂ) ∈ disk 1 ∧
        ‖diskAutomorphism (a / (ρ : ℂ)) (b / (ρ : ℂ))‖ ≤ symmetricPseudodistance q := by
  obtain ⟨r, hr, hrh, hbound⟩ := compact_strict_pseudodiameter hU hU1 hdiam hK hne hKU
  obtain ⟨q, hq, hqr, hrq⟩ := exists_uniform_symmetric_radius hr hrh
  have hnear : ∀ᶠ ρ : ℝ in 𝓝 1, ∀ p ∈ K ×ˢ K,
      p.1 / (ρ : ℂ) ∈ disk 1 ∧ p.2 / (ρ : ℂ) ∈ disk 1 ∧
      ‖diskAutomorphism (p.1 / (ρ : ℂ)) (p.2 / (ρ : ℂ))‖ < symmetricPseudodistance q := by
    apply (hK.prod hK).eventually_forall_of_forall_eventually
    intro p hp
    have hp1 : p.1 ∈ disk 1 := hU1 (hKU hp.1)
    have hp2 : p.2 ∈ disk 1 := hU1 (hKU hp.2)
    have hc1 : ContinuousAt (fun v : ℝ × (ℂ × ℂ) => v.2.1 / (v.1 : ℂ)) (1, p) :=
      (continuous_fst.comp continuous_snd).continuousAt.div
        (Complex.continuous_ofReal.comp continuous_fst).continuousAt (by norm_num)
    have hc2 : ContinuousAt (fun v : ℝ × (ℂ × ℂ) => v.2.2 / (v.1 : ℂ)) (1, p) :=
      (continuous_snd.comp continuous_snd).continuousAt.div
        (Complex.continuous_ofReal.comp continuous_fst).continuousAt (by norm_num)
    have hpair := hc1.prodMk hc2
    have hauto : ContinuousAt (fun v : ℂ × ℂ => ‖diskAutomorphism v.1 v.2‖) p :=
      diskAutomorphism_joint_continuous.norm.continuousAt
        ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hp1, hp2⟩)
    have hc : ContinuousAt (fun v : ℝ × (ℂ × ℂ) =>
        ‖diskAutomorphism (v.2.1 / (v.1 : ℂ)) (v.2.2 / (v.1 : ℂ))‖) (1, p) := by
      have hauto' : ContinuousAt (fun v : ℂ × ℂ => ‖diskAutomorphism v.1 v.2‖)
          (p.1 / ((1 : ℝ) : ℂ), p.2 / ((1 : ℝ) : ℂ)) := by simpa using hauto
      exact ContinuousAt.comp (x := (1, p))
        (f := fun v : ℝ × (ℂ × ℂ) => (v.2.1 / (v.1 : ℂ), v.2.2 / (v.1 : ℂ)))
        (g := fun v : ℂ × ℂ => ‖diskAutomorphism v.1 v.2‖) hauto' hpair
    have he1 : ∀ᶠ v : ℝ × (ℂ × ℂ) in 𝓝 (1, p), v.2.1 / (v.1 : ℂ) ∈ disk 1 :=
      hc1.preimage_mem_nhds (by simpa [disk] using isOpen_ball.mem_nhds hp1)
    have he2 : ∀ᶠ v : ℝ × (ℂ × ℂ) in 𝓝 (1, p), v.2.2 / (v.1 : ℂ) ∈ disk 1 :=
      hc2.preimage_mem_nhds (by simpa [disk] using isOpen_ball.mem_nhds hp2)
    have he3 := hc.eventually (gt_mem_nhds (show
      ‖diskAutomorphism (p.1 / ((1 : ℝ) : ℂ)) (p.2 / ((1 : ℝ) : ℂ))‖ < symmetricPseudodistance q by
        simpa using (hbound p.2 hp.2 p.1 hp.1).trans_lt hrq))
    filter_upwards [he1, he2, he3] with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ₀ := max (1 - δ / 2) (1 / 2)
  have hρ₀ : 0 < ρ₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)
  have hρ₀1 : ρ₀ < 1 := max_lt (by linarith) (by norm_num)
  refine ⟨q, ρ₀, hq, hqr, hρ₀, hρ₀1, ?_⟩
  intro ρ hρ a ha b hb
  have hρnear : ρ ∈ ball (1 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    have := (le_max_left (1 - δ / 2) (1 / 2)).trans hρ.1
    constructor <;> linarith [hρ.2]
  have h := hδsub hρnear (a, b) ⟨ha, hb⟩
  exact ⟨h.1, h.2.1, h.2.2.le⟩

end ModifiedCartan
