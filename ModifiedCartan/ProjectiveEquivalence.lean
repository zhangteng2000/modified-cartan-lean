import ModifiedCartan.ProjectivePartitions
import ModifiedCartan.ProjectiveCurves

noncomputable section
set_option autoImplicit false
open Set Filter Topology Finset Manifold
open scoped LinearAlgebra.Projectivization Manifold
namespace ModifiedCartan

/-- Product of the genuine projective spaces on the parts of a partition. -/
abbrev ProjectivePartitionProduct {p : ℕ} (P : IndexPartition p) :=
  ∀ I : P.parts, ℙ ℂ (Fin I.val.card → ℂ)

def projectivePartitionProjection {p : ℕ} (P : IndexPartition p)
    (q : ProjectiveX p) : ProjectivePartitionProduct P :=
  fun I => projectiveProjection I.val (P.nonempty_of_mem_parts I.property) q

def projectiveProductHyperplane {p : ℕ} (P : IndexPartition p) : Set (ProjectivePartitionProduct P) :=
  {g | ∀ I : P.parts, g I ∈ projectiveHyperplane I.val.card}

/-- Holomorphy in the standard product affine charts. -/
def ProjectiveProductHolomorphicOn {p : ℕ} {P : IndexPartition p}
    (G : ℂ → ProjectivePartitionProduct P) (U : Set ℂ) : Prop :=
  ∀ I : P.parts, ProjectiveHolomorphicOn (fun z => G z I) U

/-- The manuscript's geometric partition assertion: arbitrary holomorphic
maps into the actual complex manifold X_p, followed by actual coordinate
projections, converge locally uniformly in the product projective topology
to a holomorphic map with values in the product of the zero-sum hyperplanes. -/
def ProjectiveMapPartitionProperty {p : ℕ} (base : Fin p) [Nonempty (ProjectiveX p)] (U : Set ℂ) : Prop :=
  letI := projectiveXChartedSpace base
  ∀ F : ℕ → ℂ → ProjectiveX p,
    (∀ n, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, normalizedDirectionSubspace base) (F n) (disk 1)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : IndexPartition p,
      ∃ G : ℂ → ProjectivePartitionProduct P,
        ProjectiveProductHolomorphicOn G U ∧ MapsTo G U (projectiveProductHyperplane P) ∧
        TendstoLocallyUniformlyOn (fun n z => projectivePartitionProjection P (F (φ n) z)) G atTop U

theorem partitionProperty_iff_projectiveMaps {p : ℕ} (base : Fin p) [Nonempty (ProjectiveX p)]
    {U : Set ℂ} (hne : U.Nonempty) (hU : IsOpen U) (hconn : IsPreconnected U) (hsub : U ⊆ disk 1) :
    PartitionProperty p U ↔ ProjectiveMapPartitionProperty base U := by
  classical
  letI := projectiveXChartedSpace base
  rw [partitionProperty_iff_familyProjective hne hU hconn hsub]
  constructor
  · intro h F hF
    have hFc (n : ℕ) := (projectiveX_holomorphic_iff base Metric.isOpen_ball).mp (hF n)
    let f := projectiveCurveFamily base F
    obtain ⟨φ, hφ, P, hP⟩ := h f (projectiveCurveFamily_units base hFc) (projectiveCurveFamily_zeroSum base F)
    have hex : ∀ I : P.parts, ∃ g : ℂ → ℙ ℂ (Fin I.val.card → ℂ),
        ProjectiveHolomorphicOn g U ∧ MapsTo g U (projectiveHyperplane I.val.card) ∧
        TendstoLocallyUniformlyOn (fun n z => projectivePartitionProjection P (F (φ n) z) I) g atTop U := by
      intro I
      obtain ⟨hI, g, hg, hs, hc⟩ := hP I.val I.property
      refine ⟨g, hg, hs, hc.congr (fun n z hz => ?_)⟩
      exact projectiveProjection_curveFamily base (fun n => F (φ n)) I.val hI n z
    choose g hg hs hc using hex
    refine ⟨φ, hφ, P, fun z I => g I z, hg, fun z hz I => hs I hz, ?_⟩
    exact locallyUniform_pi (fun I => (hg I).1) hc
  · intro h f hf hs
    let q0 : ProjectiveX p := Classical.choice inferInstance
    let F := familyProjectiveCurve base q0 f hf hs
    have hF (n : ℕ) : MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, normalizedDirectionSubspace base) (F n) (disk 1) :=
      (projectiveX_holomorphic_iff base Metric.isOpen_ball).mpr
        (familyProjectiveCurve_holomorphic base q0 f hf hs n)
    obtain ⟨φ, hφ, P, G, hG, hmaps, hc⟩ := h F hF
    refine ⟨φ, hφ, P, fun I hI => ?_⟩
    let i : P.parts := ⟨I, hI⟩
    have hneI := P.nonempty_of_mem_parts hI
    refine ⟨hneI, fun z => G z i, hG i, fun z hz => hmaps hz i, ?_⟩
    have hcomp := (Pi.uniformContinuous_proj _ i).comp_tendstoLocallyUniformlyOn hc
    apply hcomp.congr
    intro n z hz
    exact projectiveProjection_familyCurve base q0 f hf hs I hneI (φ n) (hsub hz)

/-- Proposition prop:projective-equivalence, with the manuscript's full range
p >= 3 and 0 < R <= 1 and no altered radius. -/
theorem projective_equivalence {p : ℕ} (hp : 3 ≤ p) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    letI : Nonempty (ProjectiveX p) := projectiveX_nonempty (by omega)
    PartitionProperty p (disk R) ↔ ProjectiveMapPartitionProperty (⟨0, by omega⟩ : Fin p) (disk R) := by
  letI : Nonempty (ProjectiveX p) := projectiveX_nonempty (by omega)
  apply partitionProperty_iff_projectiveMaps (⟨0, by omega⟩ : Fin p)
  · exact ⟨0, by simpa [disk] using hR⟩
  · exact Metric.isOpen_ball
  · exact (convex_ball (0 : ℂ) R).isPreconnected
  · exact Metric.ball_subset_ball hR1

end ModifiedCartan
