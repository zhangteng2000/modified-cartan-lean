import ModifiedCartan.NormalizedWronskian
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

/-- Multiplication by a common analytic factor acts on derivative jets by an
actual triangular matrix, so it multiplies the Wronskian by its m-th power. -/
theorem wronskian_common_factor {m : ℕ} {g : Fin m → ℂ → ℂ} {h : ℂ → ℂ} {z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) z) (hh : AnalyticAt ℂ h z) :
    wronskian (fun j w => h w*g j w) z = h z^m * wronskian g z := by
  classical
  let A : Matrix (Fin m) (Fin m) ℂ := .of fun i j => iteratedDeriv (i : ℕ) (g j) z
  let T : Matrix (Fin m) (Fin m) ℂ := .of fun i k =>
    ((i : ℕ).choose (k : ℕ) : ℂ) * iteratedDeriv ((i : ℕ)-(k : ℕ)) h z
  have hmatrix : (.of fun i j : Fin m => iteratedDeriv (i : ℕ) (fun w => h w*g j w) z) = T*A := by
    ext i j
    simp only [Matrix.of_apply,Matrix.mul_apply,T,A]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (((i : ℕ).choose k : ℂ) * iteratedDeriv ((i : ℕ)-k) h z) * iteratedDeriv k (g j) z)]
    have hprod : (fun w => h w*g j w) = fun w => g j w*h w := by ext w; ring
    rw [hprod,iteratedDeriv_fun_mul (hg j).contDiffAt hh.contDiffAt]
    have hsum : (∑ k ∈ Finset.range ((i : ℕ)+1),
        (((i : ℕ).choose k : ℂ) * iteratedDeriv ((i : ℕ)-k) h z) * iteratedDeriv k (g j) z) =
      ∑ k ∈ Finset.range m,
        (((i : ℕ).choose k : ℂ) * iteratedDeriv ((i : ℕ)-k) h z) * iteratedDeriv k (g j) z := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hki
      have hik : (i : ℕ) < k := by simp only [Finset.mem_range,not_lt] at hki; omega
      simp [Nat.choose_eq_zero_of_lt hik]
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have htri : T.IsLowerTriangular := by
    intro i j hij
    dsimp [T]
    simp [Nat.choose_eq_zero_of_lt (show (i : ℕ) < (j : ℕ) from hij)]
  have hdet : T.det = h z^m := by
    rw [Matrix.det_of_isLowerTriangular T htri]
    simp [T,iteratedDeriv_zero]
  change Matrix.det _ = _
  rw [hmatrix,Matrix.det_mul,hdet]
  rfl

/-- Normalized Wronskians are invariant under a common nonzero holomorphic
factor. This is genuine cancellation in the derivative determinant. -/
theorem normalizedWronskian_common_factor {m : ℕ} {g : Fin m → ℂ → ℂ}
    {h : ℂ → ℂ} {z : ℂ} (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hh : AnalyticAt ℂ h z) (hn : h z ≠ 0) :
    normalizedWronskian (fun j w => h w*g j w) z = normalizedWronskian g z := by
  unfold normalizedWronskian
  rw [wronskian_common_factor hg hh,Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_div_mul_left _ _ (pow_ne_zero m hn)

theorem normalizedWronskian_common_divisor {m : ℕ} {g : Fin m → ℂ → ℂ}
    {h : ℂ → ℂ} {z : ℂ} (hg : ∀ j, AnalyticAt ℂ (g j) z)
    (hh : AnalyticAt ℂ h z) (hn : h z ≠ 0) :
    normalizedWronskian (fun j w => g j w/h w) z = normalizedWronskian g z := by
  simpa only [div_eq_inv_mul,Pi.inv_def] using
    normalizedWronskian_common_factor hg (hh.inv hn) (inv_ne_zero hn)

end ModifiedCartan
