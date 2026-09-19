import ModifiedCartan.CountableExtraction
import ModifiedCartan.TailClasses
import ModifiedCartan.CClassExhaustion
import ModifiedCartan.UnitDiskExhaustion
import ModifiedCartan.FiveClassReduction

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- Actual countable extraction upgrades the classical alternative from
all strict interior disks to the full open unit disk. -/
theorem cartanExtraction_of_local {p : ℕ}
    (hlocal : ∀ f : Family p, UnitFamily f → ZeroSum f → ∀ L : ℝ, 0 < L → L < 1 →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (IsCClass (subsequence f φ) Finset.univ (disk L) ∨
         ∃ I J : Finset (Fin p), Disjoint I J ∧
           IsCClass (subsequence f φ) I (disk L) ∧ IsCClass (subsequence f φ) J (disk L))) :
    CartanExtractionAt p := by
  intro f hf hs
  let P : ℕ → (ℕ → ℕ) → Prop := fun n φ =>
    IsCClass (subsequence f φ) Finset.univ (disk (unitDiskExhaustionRadius n)) ∨
      ∃ I J : Finset (Fin p), Disjoint I J ∧
        IsCClass (subsequence f φ) I (disk (unitDiskExhaustionRadius n)) ∧
        IsCClass (subsequence f φ) J (disk (unitDiskExhaustionRadius n))
  have hhered : ∀ n (φ ψ : ℕ → ℕ), StrictMono φ → StrictMono ψ → P n φ → P n (φ ∘ ψ) := by
    intro n φ ψ _ hψ hc
    rcases hc with hfull | ⟨I,J,hd,hI,hJ⟩
    · exact Or.inl (cclass_subsequence hfull hψ)
    · exact Or.inr ⟨I,J,hd,cclass_subsequence hI hψ,cclass_subsequence hJ hψ⟩
  have hextract : ∀ n (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P n (φ ∘ ψ) := by
    intro n φ _
    exact hlocal (subsequence f φ) (unitFamily_subsequence hf φ) (zeroSum_subsequence hs φ)
      (unitDiskExhaustionRadius n) (unitDiskExhaustionRadius_pos n) (unitDiskExhaustionRadius_lt_one n)
  obtain ⟨δ,hδ,hall⟩ := countable_subsequence_selection P hhered hextract
  refine ⟨δ,hδ,cartan_alternative_of_exhaustion unitDiskExhaustion_compact_cover ?_⟩
  intro n
  obtain ⟨N,hN⟩ := hall n
  have hsub : disk (unitDiskExhaustionRadius n) ⊆ disk 1 :=
    ball_subset_ball (unitDiskExhaustionRadius_lt_one n).le
  have hu : ∀ i k, IsHolomorphicUnit (subsequence f δ i k) (disk (unitDiskExhaustionRadius n)) :=
    fun i k => ⟨(hf i (δ k)).1.mono hsub,fun z hz => (hf i (δ k)).2 z (hsub hz)⟩
  rcases hN with hfull | ⟨I,J,hd,hI,hJ⟩
  · exact Or.inl (cclass_of_tail hu hfull)
  · exact Or.inr ⟨I,J,hd,cclass_of_tail hu hI,cclass_of_tail hu hJ⟩

end ModifiedCartan
