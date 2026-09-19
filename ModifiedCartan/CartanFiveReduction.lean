import ModifiedCartan.CartanFourAnnulus
import ModifiedCartan.CartanPairUnmerge
import ModifiedCartan.AnnulusFilling
import ModifiedCartan.CartanDiagonal

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- The finite quotient-limit reduction for five functions, with all original
indices restored and the two disjoint classes retained when they occur. -/
theorem five_alternative_of_finite_ratio_limit {f : Family 5} (hf : UnitFamily f) (hs : ZeroSum f)
    {a b : Fin 5} (hab : a ≠ b) {H : ℂ → ℂ}
    (hlim : CompactConvergence (fun n z => f a n z/f b n z) H (disk 1))
    (hH : ∃ z ∈ disk 1, H z ≠ -1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (IsCClass (subsequence f φ) Finset.univ (disk r) ∨
       ∃ I J : Finset (Fin 5), Disjoint I J ∧
         IsCClass (subsequence f φ) I (disk r) ∧ IsCClass (subsequence f φ) J (disk r)) := by
  obtain ⟨α,β,hrα,hαβ,hβ1,N,hsum,hleft,hright,hback⟩ :=
    pair_merge_on_annulus hr hr1 (hf a) (hf b) hlim hH
  let U := complexAnnulus α β
  have hα : 0 < α := hr.trans_lt hrα
  have hU1 : U ⊆ disk 1 := fun z hz => by simpa [disk] using hz.2.trans hβ1
  let g : Family 5 := subsequence f (fun n => N+n)
  have hg : ∀ i n, IsHolomorphicUnit (g i n) U := fun i n =>
    ⟨(hf i (N+n)).1.mono hU1,fun z hz => (hf i (N+n)).2 z (hU1 hz)⟩
  let assign := pairAssignment a b hab
  have hm := mergedFamily_pair_unit hg a b hab hsum
  have hms : ∀ n z, z ∈ U → ∑ j, mergedFamily g assign j n z = 0 := by
    intro n z hz
    change (∑ j, ∑ i ∈ assignmentPart assign j, g i n z) = 0
    rw [assignmentPart_sum]
    exact hs (N+n) z (hU1 hz)
  obtain ⟨ψ,hψ,hc⟩ := cartan_four_annulus hα hαβ hm hms
  have hrestore (I : Finset (Fin 4))
      (hI : IsCClass (subsequence (mergedFamily g assign) ψ) I U) :
      IsCClass (subsequence f (fun n => N+ψ n)) (liftedIndices assign I) U := by
    exact cclass_unmerge_pair (fun i n => hg i (ψ n)) a b hab
      (fun n => hsum (ψ n)) (locallyBounded_subsequence hleft ψ)
      (locallyBounded_subsequence hright ψ) (locallyBounded_subsequence hback ψ) hI
  let ρ := (α+β)/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hrρ : r ≤ ρ := by dsimp [ρ]; linarith
  have hcircle : sphere (0 : ℂ) ρ ⊆ U := by
    intro z hz
    have hn : ‖z‖ = ρ := by simpa using hz
    change α < ‖z‖ ∧ ‖z‖ < β
    rw [hn]
    dsimp [ρ]
    constructor <;> linarith
  have hfill (I : Finset (Fin 4))
      (hI : IsCClass (subsequence (mergedFamily g assign) ψ) I U) :
      IsCClass (subsequence f (fun n => N+ψ n)) (liftedIndices assign I) (disk r) :=
    cclass_mono (cclass_fill_disk hρ hρ1 (fun i n => hf i (N+ψ n)) hcircle (hrestore I hI))
      (ball_subset_ball hrρ)
  refine ⟨fun n => N+ψ n,fun i j hij => Nat.add_lt_add_left (hψ hij) N,?_⟩
  rcases hc with hfull | ⟨I,J,hd,hI,hJ⟩
  · left
    simpa only [liftedIndices_univ] using hfill Finset.univ hfull
  · exact Or.inr ⟨liftedIndices assign I,liftedIndices assign J,liftedIndices_disjoint assign hd,
      hfill I hI,hfill J hJ⟩

theorem five_global_alternative_of_finite_ratio_limit {f : Family 5} (hf : UnitFamily f) (hs : ZeroSum f)
    {a b : Fin 5} (hab : a ≠ b) {H : ℂ → ℂ}
    (hlim : CompactConvergence (fun n z => f a n z/f b n z) H (disk 1))
    (hH : ∃ z ∈ disk 1, H z ≠ -1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (IsCClass (subsequence f φ) Finset.univ (disk 1) ∨
       ∃ I J : Finset (Fin 5), Disjoint I J ∧
         IsCClass (subsequence f φ) I (disk 1) ∧ IsCClass (subsequence f φ) J (disk 1)) := by
  apply cartan_alternative_of_local_subsequences hf
  intro φ hφ L hL hL1
  exact five_alternative_of_finite_ratio_limit (unitFamily_subsequence hf φ) (zeroSum_subsequence hs φ)
    hab (compactConvergence_subsequence hlim hφ) hH hL.le hL1

end ModifiedCartan
