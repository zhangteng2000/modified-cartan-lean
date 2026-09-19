import ModifiedCartan.CartanPairOverlap

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

/-- The first excluded reduction case in Cartan's induction. -/
def NoVanishingQuotientSubsequence {p : ℕ} (f : Family p) (U : Set ℂ) : Prop :=
  ∀ i j, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
    CompactConvergence (fun n z => f i (φ n) z / f j (φ n) z) (fun _ => 0) U

/-- Once the finite-limit reduction case is excluded, a unit quotient limit
of distinct indices can only be minus one. This is an explicit branch condition. -/
def OnlyNegativeOneUnitLimits {p : ℕ} (f : Family p) (U : Set ℂ) : Prop :=
  ∀ i j, i ≠ j → ∀ φ : ℕ → ℕ, StrictMono φ → ∀ G : ℂ → ℂ,
    IsHolomorphicUnit G U → CompactConvergence (fun n z => f i (φ n) z / f j (φ n) z) G U →
      ∀ z ∈ U, G z = -1

theorem noVanishingQuotientSubsequence_subsequence {p : ℕ} {f : Family p} {U : Set ℂ}
    (h : NoVanishingQuotientSubsequence f U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    NoVanishingQuotientSubsequence (subsequence f φ) U := by
  intro i j hex
  obtain ⟨ψ, hψ, hlim⟩ := hex
  exact h i j ⟨φ ∘ ψ, hφ.comp hψ, hlim⟩

theorem onlyNegativeOneUnitLimits_subsequence {p : ℕ} {f : Family p} {U : Set ℂ}
    (h : OnlyNegativeOneUnitLimits f U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    OnlyNegativeOneUnitLimits (subsequence f φ) U := by
  intro i j hij ψ hψ G hG hlim
  exact h i j hij (φ ∘ ψ) (hφ.comp hψ) G hG hlim

theorem ratio_neg_one_of_logDerivative_bound {p : ℕ} {f : Family p} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hf : ∀ i n, IsHolomorphicUnit (f i n) (disk T))
    (hno : NoVanishingQuotientSubsequence f (disk T))
    (hfinite : OnlyNegativeOneUnitLimits f (disk T)) {i j : Fin p} (hij : i ≠ j)
    (hb : ∀ n z, z ∈ disk T → ‖logDeriv (fun w => f i n w / f j n w) z‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => f i (φ n) z / f j (φ n) z) (fun _ => -1) (disk T) := by
  obtain ⟨φ, hφ, G, hG, hlim⟩ := ratio_unit_limit_of_logDerivative_bound hT hC hf i j hb (hno i j) (hno j i)
  exact ⟨φ, hφ, (compactConvergence_iff Metric.isOpen_ball).mpr
    (((compactConvergence_iff Metric.isOpen_ball).mp hlim).congr_right
      (hfinite i j hij φ hφ G hG hlim))⟩

/-- The complete first logarithmic-derivative branch of Cartan's induction:
two distinct bounded pairs yield two disjoint C classes after extraction,
once the two previously reducible cases have been excluded. -/
theorem cartan_two_bounded_pairs {p : ℕ} {f : Family p} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hf : ∀ i n, IsHolomorphicUnit (f i n) (disk T))
    (hno : NoVanishingQuotientSubsequence f (disk T))
    (hfinite : OnlyNegativeOneUnitLimits f (disk T))
    {a b c d : Fin p} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : ({a, b} : Finset (Fin p)) ≠ {c, d})
    (h1 : ∀ n z, z ∈ disk T → ‖logDeriv (fun w => f a n w / f b n w) z‖ ≤ C)
    (h2 : ∀ n z, z ∈ disk T → ‖logDeriv (fun w => f c n w / f d n w) z‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Disjoint ({a, b} : Finset (Fin p)) {c, d} ∧
      IsCClass (subsequence f φ) {a, b} (disk T) ∧
      IsCClass (subsequence f φ) {c, d} (disk T) := by
  obtain ⟨φ, hφ, hlim1⟩ := ratio_neg_one_of_logDerivative_bound hT hC hf hno hfinite hab h1
  obtain ⟨ψ, hψ, hlim2⟩ := ratio_neg_one_of_logDerivative_bound hT hC
    (fun i n => hf i (φ n)) (noVanishingQuotientSubsequence_subsequence hno hφ)
    (onlyNegativeOneUnitLimits_subsequence hfinite hφ) hcd (fun n => h2 (φ n))
  have hlim1' := compactConvergence_subsequence hlim1 hψ
  have hf' : ∀ i n, IsHolomorphicUnit (subsequence f (φ ∘ ψ) i n) (disk T) :=
    fun i n => hf i (φ (ψ n))
  rcases cancelling_pairs_disjoint_or_ratio_one Metric.isOpen_ball hf' hab hcd hne hlim1' hlim2 with hd | ⟨i, j, hij, hone⟩
  · exact ⟨φ ∘ ψ, hφ.comp hψ, hd, cclass_pair_of_ratio_neg_one hf' hab hlim1',
      cclass_pair_of_ratio_neg_one hf' hcd hlim2⟩
  · have hh := hfinite i j hij (φ ∘ ψ) (hφ.comp hψ) (fun _ => 1)
      ⟨differentiableOn_const 1, fun _ _ => one_ne_zero⟩ hone 0 (by simpa [disk] using hT)
    norm_num at hh

end ModifiedCartan
