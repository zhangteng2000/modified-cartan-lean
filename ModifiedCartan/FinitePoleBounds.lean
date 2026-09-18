import ModifiedCartan.ReflectedDerivatives
import ModifiedCartan.LogDerivativeProducts

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Metric Set
namespace ModifiedCartan

/-- Sum the principal and reflected pole bounds in an actual Blaschke factorization. -/
theorem finite_pole_derivative_bound {F Q : ℂ → ℂ} (s : Finset ℂ) (m : ℂ → ℕ)
    {r T S : ℝ} (hr : 0 ≤ r) (hrT : r < T) (hTS : T < S)
    (hs : ∀ a ∈ s, ‖a‖ ≤ T)
    (hQ : AnalyticOnNhd ℂ Q (closedBall (0 : ℂ) T))
    (hQnz : ∀ z ∈ closedBall (0 : ℂ) T, Q z ≠ 0)
    (hfact : ∀ z ∈ closedBall (0 : ℂ) S,
      F z = (∏ a ∈ s, blaschkeFactor S a z ^ m a) * Q z)
    (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) (hzs : z ∉ s) :
    ‖iteratedDeriv n (logDeriv F) z‖ ≤
      (∑ a ∈ s, (m a : ℝ) * ((n.factorial : ℝ) * ‖z - a‖ ^ (-1 - (n : ℤ)))) +
      ((∑ a ∈ s, m a : ℕ) : ℝ) *
        ((n.factorial : ℝ) * (2 / (S - r)) / ((S - r) / 2) ^ n) +
      ‖iteratedDeriv n (logDeriv Q) z‖ := by
  classical
  have hS : 0 < S := hr.trans_lt (hrT.trans hTS)
  let U : Set ℂ := ball (0 : ℂ) T \ (s : Set ℂ)
  have hU : IsOpen U := isOpen_ball.inter s.finite_toSet.isClosed.isOpen_compl
  have hUT : U ⊆ closedBall (0 : ℂ) T := fun _ hw => ball_subset_closedBall hw.1
  have hUS : U ⊆ closedBall (0 : ℂ) S := hUT.trans (closedBall_subset_closedBall hTS.le)
  have hB : ∀ a ∈ s, AnalyticOnNhd ℂ (blaschkeFactor S a) U :=
    fun a ha => (blaschkeFactor_analytic hS ((hs a ha).trans_lt hTS)).mono hUS
  have hBnz : ∀ a ∈ s, ∀ w ∈ U, blaschkeFactor S a w ≠ 0 := by
    intro a ha w hw
    have hwa : w ≠ a := by intro he; exact hw.2 (he ▸ ha)
    exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hS.ne') (sub_ne_zero.mpr hwa))
      (blaschke_numerator_ne_zero hS ((hs a ha).trans_lt hTS) (by simpa using hUS hw))
  have hzU : z ∈ U := ⟨by simpa using hz.trans_lt hrT, hzs⟩
  rw [iterated_logDeriv_finite_factorization s m hU hB (hQ.mono hUT) hBnz
    (fun w hw => hQnz w (hUT hw)) (fun w hw => hfact w (hUS hw)) n hzU]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (norm_sum_le _ _).trans
  have hsum : (∑ a ∈ s, ‖(m a : ℂ) * iteratedDeriv n (logDeriv (blaschkeFactor S a)) z‖) ≤
      ∑ a ∈ s, (m a : ℝ) *
        ((n.factorial : ℝ) * ‖z - a‖ ^ (-1 - (n : ℤ)) +
          (n.factorial : ℝ) * (2 / (S - r)) / ((S - r) / 2) ^ n) := by
    apply Finset.sum_le_sum
    intro a ha
    rw [norm_mul, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact blaschke_logDeriv_iterated_bound hr (hrT.trans hTS) ((hs a ha).trans_lt hTS) hz
      (by intro he; exact hzs (he ▸ ha)) n
  apply hsum.trans_eq
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Nat.cast_sum]

end ModifiedCartan
