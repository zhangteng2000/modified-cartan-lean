import ModifiedCartan.ProjectiveClass
import Mathlib.Data.Finset.Sort

noncomputable section
set_option autoImplicit false
open Set Filter Topology Finset
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

def blockIndex {p : ℕ} (I : Finset (Fin p)) : Fin I.card → Fin p := I.orderEmbOfFin rfl

theorem blockIndex_mem {p : ℕ} (I : Finset (Fin p)) (j : Fin I.card) : blockIndex I j ∈ I :=
  I.orderEmbOfFin_mem rfl j

theorem blockIndex_surjective {p : ℕ} {I : Finset (Fin p)} {j : Fin p} (hj : j ∈ I) :
    ∃ k, blockIndex I k = j := by
  have hr : Set.range (blockIndex I) = (I : Set (Fin p)) := I.range_orderEmbOfFin rfl
  change j ∈ Set.range (blockIndex I)
  rwa [hr]

theorem blockIndex_sum {p : ℕ} (I : Finset (Fin p)) (g : Fin p → ℂ) :
    ∑ j : Fin I.card, g (blockIndex I j) = ∑ j ∈ I, g j := by
  calc
    _ = ∑ j ∈ univ.map (I.orderEmbOfFin rfl).toEmbedding, g j := by rw [sum_map]; rfl
    _ = _ := by rw [I.map_orderEmbOfFin_univ rfl]

def restrictedFamily {p : ℕ} (I : Finset (Fin p)) (f : Family p) : Family I.card :=
  fun j => f (blockIndex I j)

theorem restrictedFamily_cclass_iff {p : ℕ} (I : Finset (Fin p)) (f : Family p) (U : Set ℂ) :
    IsCClass (restrictedFamily I f) univ U ↔ IsCClass f I U := by
  constructor
  · rintro ⟨k, hk, hb, hs⟩
    refine ⟨blockIndex I k, blockIndex_mem I k, ?_, ?_⟩
    · intro j hj
      obtain ⟨l, rfl⟩ := blockIndex_surjective hj
      exact hb l (mem_univ l)
    · apply compactConvergence_congr hs
      intro n z _
      exact blockIndex_sum I (fun j => f j n z / f (blockIndex I k) n z)
  · rintro ⟨k, hk, hb, hs⟩
    obtain ⟨l, rfl⟩ := blockIndex_surjective hk
    refine ⟨l, mem_univ l, fun j _ => hb _ (blockIndex_mem I j), ?_⟩
    apply compactConvergence_congr hs
    intro n z _
    exact (blockIndex_sum I (fun j => f j n z / f (blockIndex I l) n z)).symm

def blockBase {p : ℕ} {I : Finset (Fin p)} (hI : I.Nonempty) : Fin I.card :=
  ⟨0, card_pos.mpr hI⟩

def blockProjective {p : ℕ} (f : Family p) (I : Finset (Fin p)) (hI : I.Nonempty) :=
  familyProjective (blockBase hI) (restrictedFamily I f)

/-- A genuine map to the projective zero-sum hyperplane on the coordinates of I. -/
def HasBlockProjectiveLimit {p : ℕ} (f : Family p) (I : Finset (Fin p)) (U : Set ℂ) : Prop :=
  ∃ hI : I.Nonempty, ∃ G : ℂ → ℙ ℂ (Fin I.card → ℂ),
    ProjectiveHolomorphicOn G U ∧ MapsTo G U (projectiveHyperplane I.card) ∧
    TendstoLocallyUniformlyOn (blockProjective f I hI) G atTop U

theorem locallyUniform_subsequence {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {F : ℕ → X → Y} {G : X → Y} {U : Set X}
    (h : TendstoLocallyUniformlyOn F G atTop U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoLocallyUniformlyOn (fun n => F (φ n)) G atTop U := by
  intro u hu z hz
  obtain ⟨V, hV, hN⟩ := h u hu z hz
  exact ⟨V, hV, hφ.tendsto_atTop.eventually hN⟩

theorem blockProjectiveLimit_subsequence {p : ℕ} {f : Family p} {I : Finset (Fin p)}
    {U : Set ℂ} (h : HasBlockProjectiveLimit f I U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    HasBlockProjectiveLimit (subsequence f φ) I U := by
  obtain ⟨hI, G, hg, hs, hc⟩ := h
  exact ⟨hI, G, hg, hs, locallyUniform_subsequence hc hφ⟩

theorem cclass_blockProjectiveLimit_subsequence {p : ℕ} {f : Family p}
    {I : Finset (Fin p)} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U) (hI : IsCClass f I U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ HasBlockProjectiveLimit (subsequence f φ) I U := by
  have hne := cclass_nonempty hI
  obtain ⟨φ, hφ, G, hg, hs, hc⟩ := cclass_univ_projective_limit (blockBase hne) hU
    (fun j n => hf (blockIndex I j) n) ((restrictedFamily_cclass_iff I f U).mpr hI)
  exact ⟨φ, hφ, hne, G, hg, hs, hc⟩

theorem cclass_of_blockProjectiveLimit {p : ℕ} {f : Family p}
    {I : Finset (Fin p)} {U : Set ℂ} (hne : U.Nonempty) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    (h : HasBlockProjectiveLimit f I U) : IsCClass f I U := by
  obtain ⟨hI, G, hg, hs, hc⟩ := h
  exact (restrictedFamily_cclass_iff I f U).mp
    (cclass_univ_of_projective_limit (blockBase hI) hne hU hconn
      (fun j n => hf (blockIndex I j) n) hs hc)

end ModifiedCartan
