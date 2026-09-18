import ModifiedCartan.Statements
import Mathlib.Analysis.MeanInequalitiesPow

noncomputable section
set_option autoImplicit false
namespace ModifiedCartan

theorem finite_sum_rpow_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, x i) ^ p ≤ ∑ i ∈ s, (x i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp.ne']
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    exact (Real.rpow_add_le_add_rpow (hx a (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg hxs) hp.le hp1).trans (add_le_add le_rfl (ih hxs))

theorem natCast_rpow_le_self (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (n : ℝ) ^ p ≤ n := by
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hp.ne']
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hp1

theorem negative_integer_power_rpow {x : ℝ} (hx : 0 ≤ x) (j : ℕ) (p : ℝ) :
    (x ^ (-(j : ℤ))) ^ p = x ^ (-(j : ℝ) * p) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul hx]
  norm_cast

theorem weighted_pole_sum_rpow_bound {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (j : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, (m i : ℝ) * x i ^ (-(j : ℤ))) ^ p ≤
      ∑ i ∈ s, (m i : ℝ) * x i ^ (-(j : ℝ) * p) := by
  apply (finite_sum_rpow_le s _ (fun i hi => mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (hx i hi) _)) hp hp1).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [Real.mul_rpow (Nat.cast_nonneg _) (zpow_nonneg (hx i hi) _),
    negative_integer_power_rpow (hx i hi)]
  exact mul_le_mul_of_nonneg_right (natCast_rpow_le_self (m i) hp hp1)
    (Real.rpow_nonneg (hx i hi) _)

end ModifiedCartan
