import ModifiedCartan.Blaschke
import ModifiedCartan.ZeroFactors
import Mathlib.Analysis.Complex.AbsMax

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Metric Set
namespace ModifiedCartan

/-- A bounded finite Blaschke decomposition retaining all smaller-disk zeros,
including boundary zeros. The remainder is analytic on the entire unit disk. -/
theorem bounded_blaschke_factorization_local {F : ℂ → ℂ} {T R M : ℝ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖F z‖ ≤ M)
    {w : ℂ} (hw : w ∈ disk 1) (hFw : F w ≠ 0)
    (hT : 0 ≤ T) (hTR : T < R) (hR1 : R < 1) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ) (Q : ℂ → ℂ),
      (∀ a ∈ s, ‖a‖ ≤ T ∧ 0 < m a) ∧
      AnalyticOnNhd ℂ Q (disk 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) T, Q z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, ‖Q z‖ ≤ M) ∧
      (∀ z ∈ closedBall (0 : ℂ) R,
        F z = (∏ a ∈ s, blaschkeFactor R a z ^ m a) * Q z) := by
  classical
  have hR : 0 < R := lt_of_le_of_lt hT hTR
  have hRsub : closedBall (0 : ℂ) R ⊆ disk 1 := closedBall_subset_ball hR1
  obtain ⟨s, m, g, hs, hg, hgnz, hfg⟩ := finite_zero_factorization hF hw hFw hT (hTR.trans hR1)
  let d : ℂ → ℂ → ℂ := fun a z => (((R ^ 2 : ℝ) : ℂ) - conj a * z) / (R : ℂ)
  let Q : ℂ → ℂ := fun z => (∏ a ∈ s, d a z ^ m a) * g z
  have hd : ∀ a, AnalyticOnNhd ℂ (d a) (disk 1) := by
    intro a z _
    dsimp [d]
    fun_prop
  have hQ : AnalyticOnNhd ℂ Q (disk 1) := by
    intro z hz
    have he : ((∏ a ∈ s, d a ^ m a) * g) = Q := by
      ext x
      simp [Q]
    rw [← he]
    exact (Finset.analyticAt_prod s (fun a _ => (hd a z hz).pow (m a))).mul (hg z hz)
  have hdnz : ∀ a ∈ s, ∀ z ∈ closedBall (0 : ℂ) R, d a z ≠ 0 := by
    intro a ha z hz
    exact div_ne_zero (blaschke_numerator_ne_zero hR ((hs a ha).1.trans_lt hTR)
      (by simpa using hz)) (Complex.ofReal_ne_zero.mpr hR.ne')
  have hfact : ∀ z ∈ closedBall (0 : ℂ) R,
      F z = (∏ a ∈ s, blaschkeFactor R a z ^ m a) * Q z := by
    intro z hz
    rw [hfg z (hRsub hz)]
    dsimp [Q]
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    rw [← mul_pow]
    congr 1
    dsimp [blaschkeFactor, d]
    rw [div_mul_div_cancel₀ (blaschke_numerator_ne_zero hR ((hs a ha).1.trans_lt hTR)
      (by simpa using hz)), mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')]
  have hQcircle : ∀ z ∈ sphere (0 : ℂ) R, ‖Q z‖ ≤ M := by
    intro z hz
    have he := congrArg norm (hfact z (sphere_subset_closedBall hz))
    have hprod : ‖∏ a ∈ s, blaschkeFactor R a z ^ m a‖ = 1 := by
      rw [norm_prod]
      apply Finset.prod_eq_one
      intro a ha
      rw [norm_pow, blaschkeFactor_norm_on_circle hR ((hs a ha).1.trans_lt hTR)
        (by simpa using hz), one_pow]
    rw [norm_mul, hprod, one_mul] at he
    rw [← he]
    exact hbound z hz
  refine ⟨s, m, Q, hs, hQ, ?_, ?_, hfact⟩
  · intro z hz
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun a ha =>
      pow_ne_zero _ (hdnz a ha z (closedBall_subset_closedBall hTR.le hz)))) (hgnz z hz)
  · intro z hz
    have hdQ : DifferentiableOn ℂ Q (closure (ball (0 : ℂ) R)) := by
      rw [closure_ball _ hR.ne']
      exact (hQ.mono hRsub).differentiableOn
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      hdQ.diffContOnCl ?_ ?_
    · simpa only [frontier_ball _ hR.ne'] using hQcircle
    · rwa [closure_ball _ hR.ne']

theorem bounded_blaschke_factorization {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hbound : ∀ z ∈ disk 1, ‖F z‖ ≤ 1)
    {w : ℂ} (hw : w ∈ disk 1) (hFw : F w ≠ 0)
    {T R : ℝ} (hT : 0 ≤ T) (hTR : T < R) (hR1 : R < 1) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ) (Q : ℂ → ℂ),
      (∀ a ∈ s, ‖a‖ ≤ T ∧ 0 < m a) ∧
      AnalyticOnNhd ℂ Q (disk 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) T, Q z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, ‖Q z‖ ≤ 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) R,
        F z = (∏ a ∈ s, blaschkeFactor R a z ^ m a) * Q z) :=
  bounded_blaschke_factorization_local hF
    (fun z hz => hbound z (sphere_subset_ball hR1 hz)) hw hFw hT hTR hR1

end ModifiedCartan
