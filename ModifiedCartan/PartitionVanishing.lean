import ModifiedCartan.FiniteEscape
import ModifiedCartan.AbsorptionTheorem

noncomputable section
set_option autoImplicit false
open Filter Topology Set Metric
namespace ModifiedCartan

/-- Absorption forces the normalized limit at every mutually escaping
representative to vanish. All rescaling factors and escape witnesses are constructed. -/
theorem normalized_limit_zero_of_escape {m : ℕ} {R ρ : ℝ}
    (hR : 0 < R) (hρ : ρ ≤ 1) (habs : AbsorptionAt m (disk ρ))
    (F h : Family (m + 1)) (H : Fin (m + 1) → ℂ → ℂ)
    (hF : ∀ i n, IsHolomorphicUnit (F i n) (disk R))
    (hh : ∀ i n, DifferentiableOn ℂ (h i n) (disk R))
    (hlim : ∀ i, CompactConvergence (h i) (H i) (disk R))
    (hsum : ∀ n z, z ∈ disk R → ∑ i, h i n z * F i n z = 0)
    (ν : Fin (m + 1))
    (he : ∀ i : Fin m, EscapesOnCompact
      (fun n z => F ν n z / F (ν.succAbove i) n z) (disk (R * ρ))) :
    ∀ z ∈ disk R, H ν z = 0 := by
  classical
  by_contra hn
  push Not at hn
  have hsub : disk (R * ρ) ⊆ disk R := ball_subset_ball
    (by nlinarith : R * ρ ≤ R)
  have hc : ∀ i n, ContinuousOn
      (fun z => F ν n z / F (ν.succAbove i) n z) (disk (R * ρ)) := by
    intro i n
    exact (((hF ν n).1.div (hF (ν.succAbove i) n).1
      (hF (ν.succAbove i) n).2).continuousOn).mono hsub
  obtain ⟨K, hK, φ, hφ, point, hpoint⟩ := finite_escape_points hc he
  let B : ℕ → ℂ := fun n => (n : ℂ) + 1
  have hB : ∀ n, B n ≠ 0 := by intro n; dsimp [B]; exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  let A : Family m := fun i n z => B n * F (ν.succAbove i) (φ n) z / F ν (φ n) z
  let a : Family m := fun i n z => h (ν.succAbove i) (φ n) z * F (ν.succAbove i) (φ n) z / F ν (φ n) z
  have hA : ∀ i n, IsHolomorphicUnit (A i n) (disk R) := by
    intro i n
    refine ⟨(((hF (ν.succAbove i) (φ n)).1.const_mul (B n)).div
      (hF ν (φ n)).1 (hF ν (φ n)).2), ?_⟩
    intro z hz
    exact div_ne_zero (mul_ne_zero (hB n) ((hF (ν.succAbove i) (φ n)).2 z hz))
      ((hF ν (φ n)).2 z hz)
  have ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk R) := fun i n =>
    (((hh (ν.succAbove i) (φ n)).mul (hF (ν.succAbove i) (φ n)).1).div
      (hF ν (φ n)).1 (hF ν (φ n)).2)
  have hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) 0 (disk R) := by
    intro i
    have hdiv := compactConvergence_div_nat (compactConvergence_subsequence (hlim (ν.succAbove i)) hφ)
      (fun n => (hh (ν.succAbove i) (φ n)).continuousOn)
    apply compactConvergence_congr hdiv
    intro n z hz
    dsimp [a, A, B]
    field_simp [(hF ν (φ n)).2 z hz, (hF (ν.succAbove i) (φ n)).2 z hz]
  have hsumid : ∀ n z, z ∈ disk R → ∑ i, a i n z = -h ν (φ n) z := by
    intro n z hz
    have hs := hsum (φ n) z hz
    rw [Fin.sum_univ_succAbove _ ν] at hs
    dsimp [a]
    rw [← Finset.sum_div]
    apply (div_eq_iff ((hF ν (φ n)).2 z hz)).mpr
    linear_combination hs
  have hsumconv : CompactConvergence (fun n z => ∑ i, a i n z)
      (fun z => -H ν z) (disk R) := by
    have hneg : CompactConvergence (fun n z => -h ν (φ n) z) (fun z => -H ν z) (disk R) := by
      intro L hL hLc
      exact ((compactConvergence_subsequence (hlim ν) hφ) L hL hLc).neg
    exact compactConvergence_congr hneg (fun n z hz => (hsumid n z hz).symm)
  have hsne : ∃ z ∈ disk R, -H ν z ≠ 0 := by
    obtain ⟨z, hz, hne⟩ := hn
    exact ⟨z, hz, neg_ne_zero.mpr hne⟩
  obtain ⟨i, ψ, hψ, hconv⟩ := absorption_rescale habs hR A a (fun z => -H ν z)
    hA ha hsmall hsumconv hsne
  have hbound := Metric.tendstoUniformlyOn_iff.mp (hconv (K i) (hK i).1 (hK i).2) 1 (by norm_num)
  obtain ⟨n, hn⟩ := hbound.exists
  have hlt : ‖(A i (ψ n) (point i (ψ n)))⁻¹‖ < 1 := by
    simpa using hn (point i (ψ n)) (hpoint i (ψ n)).1
  have hpt := (hpoint i (ψ n)).2
  have hz : point i (ψ n) ∈ disk R := hsub ((hK i).1 (hpoint i (ψ n)).1)
  have heq : (A i (ψ n) (point i (ψ n)))⁻¹ =
      (F ν (φ (ψ n)) (point i (ψ n)) / F (ν.succAbove i) (φ (ψ n)) (point i (ψ n))) / B (ψ n) := by
    dsimp [A]
    field_simp [(hF ν (φ (ψ n))).2 _ hz, (hF (ν.succAbove i) (φ (ψ n))).2 _ hz, hB (ψ n)]
  rw [heq, norm_div] at hlt
  have hnormB : ‖B (ψ n)‖ = (ψ n : ℝ) + 1 := by
    dsimp [B]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnormB] at hlt
  have hlt' := (div_lt_iff₀ (by positivity : (0 : ℝ) < ψ n + 1)).mp hlt
  nlinarith only [hpt, hlt', (show (0 : ℝ) ≤ ψ n by positivity), sq_nonneg (ψ n : ℝ)]

theorem normalized_limits_zero_of_pairwise_escape {t : ℕ} {R ρ : ℝ}
    (ht : 2 ≤ t) (hR : 0 < R) (hρ : ρ ≤ 1) (habs : AbsorptionAt (t - 1) (disk ρ))
    (F h : Family t) (H : Fin t → ℂ → ℂ)
    (hF : ∀ i n, IsHolomorphicUnit (F i n) (disk R))
    (hh : ∀ i n, DifferentiableOn ℂ (h i n) (disk R))
    (hlim : ∀ i, CompactConvergence (h i) (H i) (disk R))
    (hsum : ∀ n z, z ∈ disk R → ∑ i, h i n z * F i n z = 0)
    (he : ∀ i j, i ≠ j → EscapesOnCompact
      (fun n z => F i n z / F j n z) (disk (R * ρ))) :
    ∀ i z, z ∈ disk R → H i z = 0 := by
  cases t with
  | zero => omega
  | succ m =>
    intro i
    exact normalized_limit_zero_of_escape hR hρ habs F h H hF hh hlim hsum i
      (fun j => he i (i.succAbove j) (Fin.succAbove_ne i j).symm)

end ModifiedCartan
