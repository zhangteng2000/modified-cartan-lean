import ModifiedCartan.Extraction
import ModifiedCartan.FinitePreorder

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

def quotientPreorder {p : ℕ} (f : Family p) (U : Set ℂ)
    (hf : ∀ i n z, z ∈ U → f i n z ≠ 0) : FinitePreorder (Fin p) where
  rel i j := LocallyBounded (fun n z => f i n z / f j n z) U
  refl i := quotient_bounded_refl (hf i)
  trans := fun {_i j _k} hij hjk => quotient_bounded_trans (hf j) hij hjk

theorem disk_pow_subset_unit {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (k : ℕ) :
    disk (σ ^ k) ⊆ disk 1 := Metric.ball_subset_ball (pow_le_one₀ hσ hσ1)

theorem disk_pow_succ_subset {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (k : ℕ) :
    disk (σ ^ (k + 1)) ⊆ disk (σ ^ k) := by
  apply Metric.ball_subset_ball
  rw [pow_succ]
  exact mul_le_of_le_one_right (pow_nonneg hσ _) hσ1

def diskQuotientPreorder {p : ℕ} (f : Family p) (hf : UnitFamily f)
    (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (k : ℕ) : FinitePreorder (Fin p) :=
  quotientPreorder f (disk (σ ^ k))
    (fun i n z hz => (hf i n).2 z (disk_pow_subset_unit hσ hσ1 k hz))

/-- Full manuscript Lemma `lem:stabilization`: common analytic extraction,
actual locally bounded quotient preorders, and the maximal-class alternative. -/
theorem stabilization_lemma {p : ℕ} (hp : 1 ≤ p) {f : Family p}
    (hf : UnitFamily f) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ φ : ℕ → ℕ, ∃ _hφ : StrictMono φ,
      (∀ i j (k : Fin p), HolomorphicLimitOrEscape
        (fun n z => f i (φ n) z / f j (φ n) z) (disk (σ ^ (k : ℕ)))) ∧
      let R := diskQuotientPreorder (subsequence f φ) (unitFamily_subsequence hf φ)
        σ hσ.le hσ1.le
      ∃ l, l < p ∧ ((maximalClasses (R l)).card = 1 ∨
        (l + 1 < p ∧ ∀ x y, PreorderMaximal (R l) x → PreorderMaximal (R l) y →
          ¬ ((R l).rel x y ∧ (R l).rel y x) →
          ¬ (R (l + 1)).rel x y ∧ ¬ (R (l + 1)).rel y x)) := by
  obtain ⟨φ, hφ, hq⟩ := unitFamily_quotient_extraction hf
    (fun k : Fin p => disk (σ ^ (k : ℕ))) (fun _ => Metric.isOpen_ball)
    (fun k => disk_pow_subset_unit hσ.le hσ1.le k)
  refine ⟨φ, hφ, hq, ?_⟩
  apply finite_preorder_stabilization hp
  intro k _ i j hij
  exact locallyBounded_mono hij (disk_pow_succ_subset hσ.le hσ1.le k)

end ModifiedCartan
