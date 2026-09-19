import ModifiedCartan.WronskianPairAnchors
import ModifiedCartan.FiniteCaseExclusion

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

theorem noVanishingQuotientSubsequence_reindex {p q : ℕ} {f : Family p} {U : Set ℂ}
    (h : NoVanishingQuotientSubsequence f U) (v : Fin q → Fin p) :
    NoVanishingQuotientSubsequence (fun i => f (v i)) U :=
  fun i j => h (v i) (v j)

theorem onlyNegativeOneUnitLimits_reindex {p q : ℕ} {f : Family p} {U : Set ℂ}
    (h : OnlyNegativeOneUnitLimits f U) {v : Fin q → Fin p} (hv : Function.Injective v) :
    OnlyNegativeOneUnitLimits (fun i => f (v i)) U :=
  fun i j hij => h (v i) (v j) (hv.ne hij)

/-- With the two-pair conclusion excluded, deletion of one fixed index leaves
actual anchored pair Wronskians after a single strict extraction. -/
theorem anchored_pairs_after_omitting_one {p : ℕ} {f : Family p} {T : ℝ}
    (hp : 2 ≤ p) (hT : 0 < T) (hf : ∀ i n, IsHolomorphicUnit (f i n) (disk T))
    (hno : NoVanishingQuotientSubsequence f (disk T))
    (hfinite : OnlyNegativeOneUnitLimits f (disk T))
    (hclasses : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ I J : Finset (Fin p), Disjoint I J ∧
      IsCClass (subsequence f φ) I (disk T) ∧ IsCClass (subsequence f φ) J (disk T)) :
    ∃ a : Fin p, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n i j, i ≠ a → j ≠ a → i ≠ j →
      ∃ w : ℂ, ‖w‖ ≤ T ∧ 1 ≤ ‖normalizedWronskian ![f i (φ n),f j (φ n)] w‖ := by
  classical
  let ι := {ij : Fin p × Fin p // ij.1 < ij.2}
  haveI : Nonempty ι := ⟨⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0 : ℕ) < 1; omega⟩⟩
  let P : ι → ℕ → Prop := fun ij n =>
    ∀ z ∈ disk T, ‖logDeriv (fun w => f ij.1.1 n w/f ij.1.2 n w) z‖ ≤ 1
  have hexclude : ∀ x y : ι, x ≠ y → ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P x (φ n) ∧ P y (φ n) := by
    intro x y hxy hsub
    obtain ⟨φ,hφ,hP⟩ := hsub
    have hsets : ({x.1.1,x.1.2} : Finset (Fin p)) ≠ {y.1.1,y.1.2} := by
      intro he
      have hx : x.1.1 = y.1.1 ∨ x.1.1 = y.1.2 := by
        have hm : x.1.1 ∈ ({y.1.1,y.1.2} : Finset (Fin p)) := he ▸ (by simp)
        simpa using hm
      have hx' : x.1.2 = y.1.1 ∨ x.1.2 = y.1.2 := by
        have hm : x.1.2 ∈ ({y.1.1,y.1.2} : Finset (Fin p)) := he ▸ (by simp)
        simpa using hm
      have he1 : x.1.1 = y.1.1 := by have := x.2; have := y.2; omega
      have he2 : x.1.2 = y.1.2 := by have := x.2; have := y.2; omega
      exact hxy (Subtype.ext (Prod.ext he1 he2))
    obtain ⟨ψ,hψ,hd,hI,hJ⟩ := cartan_two_bounded_pairs hT (by norm_num : (0 : ℝ) ≤ 1)
      (fun i n => hf i (φ n)) (noVanishingQuotientSubsequence_subsequence hno hφ)
      (onlyNegativeOneUnitLimits_subsequence hfinite hφ) (ne_of_lt x.2) (ne_of_lt y.2)
      hsets (fun n => (hP n).1) (fun n => (hP n).2)
    exact hclasses ⟨φ ∘ ψ,hφ.comp hψ,_,_,hd,hI,hJ⟩
  obtain ⟨x,φ,hφ,hfail⟩ := subsequence_all_but_one_fail P
    (eventually_at_most_one_of_no_two_subsequences P hexclude)
  refine ⟨x.1.1,φ,hφ,?_⟩
  intro n i j hi hj hij
  by_cases hlt : i < j
  · let y : ι := ⟨(i,j),hlt⟩
    have hy : y ≠ x := by intro he; exact hi (congrArg (fun e : ι => e.1.1) he)
    exact pair_anchor_of_not_logDerivative_bound (hf i (φ n)) (hf j (φ n)) (hfail n y hy)
  · have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
    let y : ι := ⟨(j,i),hjlt⟩
    have hy : y ≠ x := by intro he; exact hj (congrArg (fun e : ι => e.1.1) he)
    obtain ⟨w,hw,hW⟩ := pair_anchor_of_not_logDerivative_bound (hf j (φ n)) (hf i (φ n)) (hfail n y hy)
    refine ⟨w,hw,?_⟩
    have he : normalizedWronskian ![f i (φ n),f j (φ n)] w =
        -normalizedWronskian ![f j (φ n),f i (φ n)] w := by
      simp only [normalizedWronskian,wronskian_two,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    simpa only [he,norm_neg] using hW

end ModifiedCartan
