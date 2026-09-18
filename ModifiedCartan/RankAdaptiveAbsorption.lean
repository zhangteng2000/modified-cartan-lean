import ModifiedCartan.FunctionRank

noncomputable section
set_option autoImplicit false
open Filter Topology Set
namespace ModifiedCartan

/-- Corollary `cor:rank-adaptive-absorption`, using rank of restrictions to the
unit disk and the same exact r_d. Bounded elimination avoids any basis assumption. -/
theorem rank_adaptive_absorption {K : ℕ → ℝ} (hK : WronskianExponents K)
    (hKm : ∀ m : ℕ, (m : ℝ) ≤ K m) :
    ∀ m d : ℕ, 1 ≤ d → d ≤ m → ∀ (A a : Family m) (s : ℂ → ℂ),
      UnitFamily A → (∀ i n, DifferentiableOn ℂ (a i n) (disk 1)) →
      (∀ i, CompactConvergence (fun n z => a i n z / A i n z) (fun _ => 0) (disk 1)) →
      CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1) →
      (∃ z ∈ disk 1, s z ≠ 0) →
      (∀ n, functionRank (fun i => a i n) (disk 1) ≤ d) →
      ∃ i : Fin m, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        CompactConvergence (fun n z => (A i (φ n) z)⁻¹) (fun _ => 0) (disk (absorptionRadius K d)) := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro d hd hdm A a s hA ha hsmall hsum hsne hrank
    by_cases hmd : m = d
    · subst m
      exact absorption_at_recursive_radius hK hKm d hd A a s hA ha hsmall hsum hsne
    have hdlt : d < m := by omega
    cases m with
    | zero => omega
    | succ m =>
      have hrelation := fun n => functionRank_relation ((hrank n).trans_lt hdlt)
      choose c j hc hmax hcomb using hrelation
      obtain ⟨j₀, φ, hφ, hfixed⟩ := finite_constant_subsequence j
      have hc0 : ∀ n, c (φ n) j₀ ≠ 0 := by
        intro n
        simpa only [hfixed n] using hc (φ n)
      have hmax0 : ∀ n i, ‖c (φ n) i‖ ≤ ‖c (φ n) j₀‖ := by
        intro n i
        simpa only [hfixed n] using hmax (φ n) i
      let b : Fin m → ℕ → ℂ := fun i n => 1 - c (φ n) (j₀.succAbove i) / c (φ n) j₀
      have hb : ∀ i n, ‖b i n‖ ≤ 2 := by
        intro i n
        have hdiv : ‖c (φ n) (j₀.succAbove i) / c (φ n) j₀‖ ≤ 1 := by
          rw [norm_div]
          exact (div_le_one (norm_pos_iff.mpr (hc0 n))).mpr (hmax0 n _)
        have hh := norm_sub_le (1 : ℂ) (c (φ n) (j₀.succAbove i) / c (φ n) j₀)
        dsimp [b]
        norm_num only [norm_one] at hh
        linarith
      let A' : Family m := fun i n => A (j₀.succAbove i) (φ n)
      let a' : Family m := fun i n z => b i n * a (j₀.succAbove i) (φ n) z
      have hA' : UnitFamily A' := fun i n => hA (j₀.succAbove i) (φ n)
      have ha' : ∀ i n, DifferentiableOn ℂ (a' i n) (disk 1) :=
        fun i n => (ha (j₀.succAbove i) (φ n)).const_mul (b i n)
      have hsmall' : ∀ i, CompactConvergence (fun n z => a' i n z / A' i n z) (fun _ => 0) (disk 1) := by
        intro i
        have hbb : LocallyBounded (fun n (_z : ℂ) => b i n) (disk 1) :=
          fun _ _ _ => ⟨2, fun n _ _ => hb i n⟩
        apply compactConvergence_congr (compactConvergence_zero_mul
          (compactConvergence_subsequence (hsmall (j₀.succAbove i)) hφ) hbb)
        intro n z _
        dsimp [a', A']
        ring
      have hsumid : ∀ n z, z ∈ disk 1 → ∑ i, a' i n z = ∑ i, a i (φ n) z := by
        intro n z hz
        have he := remove_one_coefficient_identity (fun i => a i (φ n) z) (c (φ n)) j₀ (hc0 n)
        simpa only [hcomb (φ n) z hz, zero_div, sub_zero] using he
      have hsum' : CompactConvergence (fun n z => ∑ i, a' i n z) s (disk 1) :=
        compactConvergence_congr (compactConvergence_subsequence hsum hφ)
          (fun n z hz => (hsumid n z hz).symm)
      have hrank' : ∀ n, functionRank (fun i => a' i n) (disk 1) ≤ d := by
        intro n
        exact (functionRank_scaled_subfamily (fun i => a i (φ n)) (disk 1) j₀.succAbove
          (fun i => b i n)).trans (hrank (φ n))
      obtain ⟨i, ψ, hψ, hconv⟩ := ih m (by omega) d hd (by omega) A' a' s
        hA' ha' hsmall' hsum' hsne hrank'
      exact ⟨j₀.succAbove i, φ ∘ ψ, hφ.comp hψ, hconv⟩

end ModifiedCartan
