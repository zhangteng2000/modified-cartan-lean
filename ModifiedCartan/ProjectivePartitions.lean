import ModifiedCartan.ProjectiveBlocks
import ModifiedCartan.AdmissiblePartitions

noncomputable section
set_option autoImplicit false
open Set Filter Topology Finset
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

def cpartitionIndexPartition {p : ℕ} {f : Family p} {U : Set ℂ}
    (P : CPartition f U) : IndexPartition p where
  parts := P.parts
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr P.disjoint
  sup_parts := by
    ext j
    exact ⟨fun _ => mem_univ j, fun _ => Finset.mem_sup.mpr (P.cover j)⟩
  bot_notMem := by
    intro h
    exact Finset.not_nonempty_empty (cclass_nonempty (P.classes ∅ h))

theorem cpartition_from_indexPartition {p : ℕ} {f : Family p} {U : Set ℂ}
    (P : IndexPartition p) (hP : ∀ I ∈ P.parts, IsCClass f I U) :
    Nonempty (CPartition f U) := by
  refine ⟨{ parts := P.parts, cover := ?_, disjoint := P.supIndep.pairwiseDisjoint, classes := hP }⟩
  intro j
  have hj : j ∈ P.parts.biUnion id := by rw [P.biUnion_parts]; exact mem_univ j
  exact mem_biUnion.mp hj

/-- Joint convergence to the product of the actual projective hyperplanes. -/
def FamilyProjectivePartitionProperty (p : ℕ) (U : Set ℂ) : Prop :=
  ∀ f : Family p, UnitFamily f → ZeroSum f →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : IndexPartition p,
      ∀ I ∈ P.parts, HasBlockProjectiveLimit (subsequence f φ) I U

theorem cpartition_projective_common_subsequence {p : ℕ} {f : Family p} {U : Set ℂ}
    (hU : IsOpen U) (hf : ∀ j n, IsHolomorphicUnit (f j n) U) (P : CPartition f U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ I ∈ P.parts,
      HasBlockProjectiveLimit (subsequence f φ) I U := by
  let Q : Finset (Fin p) → (ℕ → ℕ) → Prop :=
    fun I φ => I ∈ P.parts → HasBlockProjectiveLimit (subsequence f φ) I U
  obtain ⟨φ, hφ, hQ⟩ := finite_subsequence_selection Q
    (fun I φ ψ hφ hψ hI hmem => blockProjectiveLimit_subsequence (hI hmem) hψ)
    (by
      intro I φ hφ
      by_cases hI : I ∈ P.parts
      · obtain ⟨ψ, hψ, hlim⟩ := cclass_blockProjectiveLimit_subsequence hU
          (fun j n => hf j (φ n)) (cclass_subsequence (P.classes I hI) hφ)
        exact ⟨ψ, hψ, fun _ => hlim⟩
      · exact ⟨id, strictMono_id, fun hh => False.elim (hI hh)⟩)
  exact ⟨φ, hφ, hQ⟩

theorem partitionProperty_iff_familyProjective {p : ℕ} {U : Set ℂ}
    (hne : U.Nonempty) (hU : IsOpen U) (hconn : IsPreconnected U) (hsub : U ⊆ disk 1) :
    PartitionProperty p U ↔ FamilyProjectivePartitionProperty p U := by
  constructor
  · intro h f hf hs
    obtain ⟨φ, hφ, ⟨P⟩⟩ := h f hf hs
    have hfu : ∀ j n, IsHolomorphicUnit ((subsequence f φ) j n) U :=
      fun j n => ⟨(hf j (φ n)).1.mono hsub, fun z hz => (hf j (φ n)).2 z (hsub hz)⟩
    obtain ⟨ψ, hψ, hlim⟩ := cpartition_projective_common_subsequence hU hfu P
    exact ⟨φ ∘ ψ, hφ.comp hψ, cpartitionIndexPartition P, hlim⟩
  · intro h f hf hs
    obtain ⟨φ, hφ, P, hP⟩ := h f hf hs
    refine ⟨φ, hφ, cpartition_from_indexPartition P (fun I hI => ?_)⟩
    exact cclass_of_blockProjectiveLimit hne hU hconn
      (fun j n => ⟨(hf j (φ n)).1.mono hsub, fun z hz => (hf j (φ n)).2 z (hsub hz)⟩) (hP I hI)

end ModifiedCartan
