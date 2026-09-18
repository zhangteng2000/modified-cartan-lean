import ModifiedCartan.LogarithmicPoles

noncomputable section
set_option autoImplicit false
open Set
namespace ModifiedCartan

theorem logDeriv_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ z ∈ U, f z ≠ 0) :
    AnalyticOnNhd ℂ (logDeriv f) U := by
  intro z hz
  exact (hf.deriv z hz).div (hf z hz) (hnz z hz)

theorem iterated_logDeriv_finite_factorization {F Q : ℂ → ℂ} {B : ℂ → ℂ → ℂ}
    (s : Finset ℂ) (m : ℂ → ℕ) {U : Set ℂ} (hU : IsOpen U)
    (hB : ∀ a ∈ s, AnalyticOnNhd ℂ (B a) U) (hQ : AnalyticOnNhd ℂ Q U)
    (hBnz : ∀ a ∈ s, ∀ z ∈ U, B a z ≠ 0) (hQnz : ∀ z ∈ U, Q z ≠ 0)
    (hfact : ∀ z ∈ U, F z = (∏ a ∈ s, B a z ^ m a) * Q z)
    (n : ℕ) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv n (logDeriv F) z =
      (∑ a ∈ s, (m a : ℂ) * iteratedDeriv n (logDeriv (B a)) z) +
        iteratedDeriv n (logDeriv Q) z := by
  have he : EqOn (logDeriv F)
      (fun w => (∑ a ∈ s, (m a : ℂ) * logDeriv (B a) w) + logDeriv Q w) U := by
    intro w hw
    exact logDeriv_finite_factorization s m hU (fun a ha => (hB a ha).differentiableOn)
      hQ.differentiableOn hfact hw (fun a ha => hBnz a ha w hw) (hQnz w hw)
  rw [he.iteratedDeriv_of_isOpen hU n hz]
  have hda : ∀ a ∈ s, ContDiffAt ℂ n (fun w => (m a : ℂ) * logDeriv (B a) w) z := by
    intro a ha
    exact analyticAt_const.mul (logDeriv_analyticOnNhd (hB a ha) (hBnz a ha) z hz) |>.contDiffAt
  have hdQ : ContDiffAt ℂ n (logDeriv Q) z := (logDeriv_analyticOnNhd hQ hQnz z hz).contDiffAt
  rw [iteratedDeriv_fun_add (ContDiffAt.sum (fun a ha => hda a ha)) hdQ,
    iteratedDeriv_fun_sum hda]
  simp only [iteratedDeriv_const_mul_field]

theorem iterated_logDeriv_eq_log_branch {Q L : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hder : ∀ z ∈ U, deriv L z = logDeriv Q z) (n : ℕ) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv n (logDeriv Q) z = iteratedDeriv (n + 1) L z := by
  rw [iteratedDeriv_succ']
  exact (show EqOn (logDeriv Q) (deriv L) U from fun w hw => (hder w hw).symm).iteratedDeriv_of_isOpen hU n hz

end ModifiedCartan
