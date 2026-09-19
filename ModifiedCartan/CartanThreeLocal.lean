import ModifiedCartan.LocalNormality
import ModifiedCartan.ProjectiveClass
import ModifiedCartan.SmallPartitions
import ModifiedCartan.PartitionCenters

noncomputable section
set_option autoImplicit false
open Filter Topology Metric
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

/-- A partition of three units on a nonempty set has just its full class. -/
theorem cpartition_three_univ {f : Family 3} {U : Set ℂ} (hne : U.Nonempty)
    (hf : ∀ i n z, z ∈ U → f i n z ≠ 0) (P : CPartition f U) :
    IsCClass f Finset.univ U := by
  obtain ⟨I, hI, hi⟩ := P.cover 0
  have hfull : I = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    obtain ⟨J, hJ, hjJ⟩ := P.cover j
    have hneIJ : I ≠ J := fun he => hj (he.symm ▸ hjJ)
    have hd := P.disjoint I hI J hJ hneIJ
    have hi2 := cclass_card_ge_two hne hf (P.classes I hI)
    have hj2 := cclass_card_ge_two hne hf (P.classes J hJ)
    have hcard := Finset.card_le_univ (I ∪ J)
    rw [Finset.card_union_of_disjoint hd] at hcard
    simp only [Fintype.card_fin] at hcard
    omega
  simpa only [hfull] using P.classes I hI

/-- The existing positive-radius partition theorem gives a genuine local
projective limit at every point for every sequence of three units. -/
theorem three_local_projective_limit {f : Family 3} (hf : UnitFamily f) (hs : ZeroSum f)
    {a : ℂ} (ha : a ∈ disk 1) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ disk 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ G : ℂ → ℙ ℂ (Fin 3 → ℂ), ProjectiveHolomorphicOn G (ball a r) ∧
      TendstoLocallyUniformlyOn (fun n => familyProjective 0 f (φ n)) G atTop (ball a r) := by
  obtain ⟨s, hs0, _, hpart⟩ := partition_exists_positive_radius 3
  let V := {z ∈ disk 1 | ‖diskAutomorphism a z‖ < s}
  have han : ‖a‖ < 1 := by simpa [disk] using ha
  have hc : ContinuousOn (fun z => ‖diskAutomorphism a z‖) (disk 1) :=
    ((diskAutomorphism_analytic han).differentiableOn.mono ball_subset_closedBall).continuousOn.norm
  have hopen : IsOpen V := hc.isOpen_inter_preimage isOpen_ball isOpen_Iio
  have haV : a ∈ V := by
    refine ⟨ha, ?_⟩
    simpa [diskAutomorphism] using hs0
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds haV)
  have hsub : ball a r ⊆ disk 1 := fun z hz => (hrV hz).1
  have hp := partitionProperty_mono (partitionProperty_center hpart ha) hrV
  obtain ⟨φ, hφ, ⟨P⟩⟩ := hp f hf hs
  have hclass := cpartition_three_univ ⟨a, mem_ball_self hr⟩
    (fun i n z hz => (hf i (φ n)).2 z (hsub hz)) P
  obtain ⟨ψ, hψ, G, hG, _, hlim⟩ := cclass_univ_projective_limit 0 isOpen_ball
    (fun i n => ⟨(hf i (φ n)).1.mono hsub, fun z hz => (hf i (φ n)).2 z (hsub hz)⟩) hclass
  exact ⟨r, hr, hsub, φ ∘ ψ, hφ.comp hψ, G, hG, hlim⟩

/-- Three-term zero sums are equicontinuous in the scalar-invariant matrix
coordinates of actual projective space. -/
theorem three_projectiveKernel_equicontinuous {f : Family 3}
    (hf : UnitFamily f) (hs : ZeroSum f) :
    Equicontinuous (fun n (z : disk 1) => projectiveKernel (familyProjective 0 f n z)) := by
  intro a
  have hloc : EquicontinuousAt
      (fun n z => projectiveKernel (familyProjective 0 f n z)) (a : ℂ) := by
    apply equicontinuousAt_of_local_subsequence_limits
    intro σ
    let g : Family 3 := fun j n => f j (σ n)
    have hg : UnitFamily g := fun j n => hf j (σ n)
    have hgs : ZeroSum g := fun n => hs (σ n)
    obtain ⟨r, hr, _, φ, hφ, G, hG, hlim⟩ := three_local_projective_limit hg hgs a.property
    refine ⟨φ, hφ, ball (a : ℂ) r, ball_mem_nhds _ hr,
      fun z => projectiveKernel (G z), (projectiveKernel_continuous 3).comp_continuousOn hG.1, ?_⟩
    exact (CompactSpace.uniformContinuous_of_continuous (projectiveKernel_continuous 3)).comp_tendstoLocallyUniformlyOn hlim
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := Metric.equicontinuousAt_iff.mp hloc ε hε
  exact ⟨δ, hδ, fun y hy n => hh y hy n⟩

end ModifiedCartan
