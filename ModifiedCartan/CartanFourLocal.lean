import ModifiedCartan.CartanFourNoReductions
import ModifiedCartan.CartanFourDiskReduction

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- Unconditional classical extraction for four units on every prescribed
strict interior disk. The full unit-disk diagonal step is separate. -/
theorem cartan_four_local {f : Family 4} (hf : UnitFamily f) (hs : ZeroSum f)
    {L : ℝ} (hL : 0 < L) (hL1 : L < 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (IsCClass (subsequence f φ) Finset.univ (disk L) ∨
       ∃ I J : Finset (Fin 4), Disjoint I J ∧
         IsCClass (subsequence f φ) I (disk L) ∧ IsCClass (subsequence f φ) J (disk L)) := by
  classical
  have hsub : disk L ⊆ disk 1 := ball_subset_ball hL1.le
  have hu : ∀ i n, IsHolomorphicUnit (f i n) (disk L) := fun i n =>
    ⟨(hf i n).1.mono hsub,fun z hz => (hf i n).2 z (hsub hz)⟩
  by_cases hno : NoVanishingQuotientSubsequence f (disk L)
  · by_cases hfinite : OnlyNegativeOneUnitLimits f (disk L)
    · obtain ⟨φ,hφ,hc⟩ := four_two_classes_of_no_reductions hL hL1 hf hs hno hfinite
      exact ⟨φ,hφ,Or.inr hc⟩
    · unfold OnlyNegativeOneUnitLimits at hfinite
      push Not at hfinite
      obtain ⟨i,j,hij,φ,hφ,G,hG,hlim,z,hz,hne⟩ := hfinite
      obtain ⟨ψ,hψ,hc⟩ := four_disk_class_of_finite_ratio_limit hL
        (fun i n => hu i (φ n)) (fun n z hz => hs (φ n) z (hsub hz)) hij hlim ⟨z,hz,hne⟩
      exact ⟨φ ∘ ψ,hφ.comp hψ,Or.inl hc⟩
  · unfold NoVanishingQuotientSubsequence at hno
    push Not at hno
    obtain ⟨i,j,φ,hφ,hlim⟩ := hno
    have hij := vanishing_quotient_indices_ne ⟨0,by simpa [disk] using hL⟩ hu hlim
    obtain ⟨ψ,hψ,hc⟩ := four_disk_class_of_finite_ratio_limit hL
      (fun i n => hu i (φ n)) (fun n z hz => hs (φ n) z (hsub hz)) hij hlim
      ⟨0,by simpa [disk] using hL,by norm_num⟩
    exact ⟨φ ∘ ψ,hφ.comp hψ,Or.inl hc⟩

end ModifiedCartan
