import ModifiedCartan.CartanFourWronskianEndgame

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- The complete four-unit branch after excluding the initial quotient-limit
reductions. All higher-Wronskian cases are discharged internally. -/
theorem four_two_classes_of_no_reductions {f : Family 4} {L : ℝ}
    (hL : 0 < L) (hL1 : L < 1) (hf : UnitFamily f) (hs : ZeroSum f)
    (hno : NoVanishingQuotientSubsequence f (disk L))
    (hfinite : OnlyNegativeOneUnitLimits f (disk L)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ I J : Finset (Fin 4), Disjoint I J ∧
      IsCClass (subsequence f φ) I (disk L) ∧ IsCClass (subsequence f φ) J (disk L) := by
  by_contra hnone
  have hsub : disk L ⊆ disk 1 := ball_subset_ball hL1.le
  obtain ⟨a,φ,hφ,hpairs⟩ := anchored_pairs_after_omitting_one (by norm_num : 2 ≤ 4) hL
    (fun i n => ⟨(hf i n).1.mono hsub,fun z hz => (hf i n).2 z (hsub hz)⟩)
    hno hfinite hnone
  let σ : Equiv.Perm (Fin 4) := Equiv.swap (Fin.last 3) a
  let F : Family 4 := fun i n => f (σ i) (φ n)
  have hFu : UnitFamily F := fun i n => hf (σ i) (φ n)
  have hFs : ZeroSum F := by
    intro n z hz
    change (∑ i, f (σ i) (φ n) z) = 0
    rw [Equiv.sum_comp σ (fun i => f i (φ n) z)]
    exact hs (φ n) z hz
  have hFn : NoVanishingQuotientSubsequence F (disk L) :=
    noVanishingQuotientSubsequence_reindex (noVanishingQuotientSubsequence_subsequence hno hφ) σ
  have hFf : OnlyNegativeOneUnitLimits F (disk L) :=
    onlyNegativeOneUnitLimits_reindex (onlyNegativeOneUnitLimits_subsequence hfinite hφ) σ.injective
  obtain ⟨η,A,hη,hηL,hA,hanchors⟩ := quotient_anchors_on_disk_of_no_vanishing hL
    (fun i n => ⟨(hFu i n).1.mono hsub,fun z hz => (hFu i n).2 z (hsub hz)⟩) hFn
  obtain ⟨N,hN⟩ := eventually_atTop.mp hanchors
  have hshift : StrictMono (fun n : ℕ => N+n) := fun i j hij => Nat.add_lt_add_left hij N
  apply four_anchored_subfamily_impossible hL hL1 hη hηL hA
    (unitFamily_subsequence hFu _) (zeroSum_subsequence hFs _)
    (noVanishingQuotientSubsequence_subsequence hFn hshift)
    (onlyNegativeOneUnitLimits_subsequence hFf hshift) (fun n => hN (N+n) (by omega))
  intro n i j hij
  have haway (k : Fin 3) : σ k.castSucc ≠ a := by
    have he : σ (Fin.last 3) = a := Equiv.swap_apply_left _ _
    rw [← he]
    exact σ.injective.ne (Fin.castSucc_ne_last k)
  exact hpairs (N+n) (σ i.castSucc) (σ j.castSucc) (haway i) (haway j)
    (σ.injective.ne ((Fin.castSucc_injective 3).ne hij))

end ModifiedCartan
