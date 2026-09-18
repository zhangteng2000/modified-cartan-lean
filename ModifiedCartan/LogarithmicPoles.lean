import ModifiedCartan.Blaschke
import ModifiedCartan.CauchyBounds
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Metric Set
namespace ModifiedCartan

theorem iteratedDeriv_reciprocal_shift (n : ℕ) (a z : ℂ) :
    iteratedDeriv n (fun w : ℂ => 1 / (w - a)) z =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * (z - a) ^ (-1 - (n : ℤ)) := by
  rw [iteratedDeriv_comp_sub_const n (fun w : ℂ => 1 / w) a]
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_one_div (𝕜 := ℂ) n isOpen_univ (mem_univ (z - a))

theorem norm_iteratedDeriv_reciprocal_shift (n : ℕ) (a z : ℂ) :
    ‖iteratedDeriv n (fun w : ℂ => 1 / (w - a)) z‖ =
      (n.factorial : ℝ) * ‖z - a‖ ^ (-1 - (n : ℤ)) := by
  rw [iteratedDeriv_reciprocal_shift]
  simp [norm_pow, norm_zpow]

theorem logDeriv_blaschkeFactor {S : ℝ} (hS : 0 < S) {a z : ℂ}
    (ha : ‖a‖ < S) (hz : ‖z‖ ≤ S) (hza : z ≠ a) :
    logDeriv (blaschkeFactor S a) z =
      1 / (z - a) + conj a / (((S ^ 2 : ℝ) : ℂ) - conj a * z) := by
  have hSc : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hden := blaschke_numerator_ne_zero hS ha hz
  unfold blaschkeFactor
  rw [logDeriv_div (f := fun w => (S : ℂ) * (w - a))
    (g := fun w => ((S ^ 2 : ℝ) : ℂ) - conj a * w) z
    (mul_ne_zero hSc (sub_ne_zero.mpr hza)) hden (by fun_prop) (by fun_prop),
    logDeriv_const_mul (f := fun w => w - a) z (S : ℂ) hSc]
  simp [logDeriv_apply, neg_div, sub_neg_eq_add]

theorem reflected_pole_norm_bound {S r : ℝ} (hS : 0 < S) (_hr : 0 ≤ r) (hrS : r < S)
    {a z : ℂ} (ha : ‖a‖ < S) (hz : ‖z‖ ≤ r) :
    ‖conj a / (((S ^ 2 : ℝ) : ℂ) - conj a * z)‖ ≤ 1 / (S - r) := by
  have hden := blaschke_numerator_ne_zero hS ha (hz.trans hrS.le)
  have hd : 0 < ‖((S ^ 2 : ℝ) : ℂ) - conj a * z‖ := norm_pos_iff.mpr hden
  have htriangle := norm_sub_norm_le (((S ^ 2 : ℝ) : ℂ)) (conj a * z)
  have hlower : S ^ 2 - ‖a‖ * ‖z‖ ≤ ‖((S ^ 2 : ℝ) : ℂ) - conj a * z‖ := by
    simpa [norm_mul] using htriangle
  rw [norm_div, Complex.norm_conj]
  apply (div_le_div_iff₀ hd (sub_pos.mpr hrS)).mpr
  have hprod := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
  nlinarith [norm_nonneg a]

theorem logDeriv_finite_factorization {F Q : ℂ → ℂ} {B : ℂ → ℂ → ℂ}
    (s : Finset ℂ) (m : ℂ → ℕ) {U : Set ℂ} (hU : IsOpen U)
    (hB : ∀ a ∈ s, DifferentiableOn ℂ (B a) U) (hQ : DifferentiableOn ℂ Q U)
    (hfact : ∀ z ∈ U, F z = (∏ a ∈ s, B a z ^ m a) * Q z)
    {z : ℂ} (hz : z ∈ U) (hBnz : ∀ a ∈ s, B a z ≠ 0) (hQnz : Q z ≠ 0) :
    logDeriv F z = (∑ a ∈ s, (m a : ℂ) * logDeriv (B a) z) + logDeriv Q z := by
  have he : F =ᶠ[nhds z] (fun w => (∏ a ∈ s, B a w ^ m a) * Q w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hfact w hw
  rw [(logDeriv_congr_nhds he).eq_of_nhds]
  have hda : ∀ a ∈ s, DifferentiableAt ℂ (B a) z :=
    fun a ha => (hB a ha z hz).differentiableAt (hU.mem_nhds hz)
  rw [logDeriv_mul (f := fun w => ∏ a ∈ s, B a w ^ m a) (g := Q) z
    (Finset.prod_ne_zero_iff.mpr (fun a ha => pow_ne_zero _ (hBnz a ha))) hQnz
    (DifferentiableAt.fun_finsetProd (fun a ha => (hda a ha).pow _))
    ((hQ z hz).differentiableAt (hU.mem_nhds hz))]
  rw [logDeriv_prod (f := fun a w => B a w ^ m a)
    (fun a ha => pow_ne_zero _ (hBnz a ha)) (fun a ha => (hda a ha).pow _)]
  congr 1
  exact Finset.sum_congr rfl (fun a ha => logDeriv_fun_pow (hda a ha) (m a))

end ModifiedCartan
