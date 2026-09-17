import ModifiedCartan.Statements
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

noncomputable section
open scoped BigOperators
namespace ModifiedCartan

theorem wronskian_one (g : Fin 1 → ℂ → ℂ) (z : ℂ) : wronskian g z = g 0 z := by
  unfold wronskian
  rw [Matrix.det_fin_one]
  simp

/-- Independent constant scalings of the columns. -/
theorem wronskian_const_mul {m : ℕ} (g : Fin m → ℂ → ℂ) (c : Fin m → ℂ) (z : ℂ) :
    wronskian (fun j w => c j * g j w) z = (∏ j, c j) * wronskian g z := by
  unfold wronskian
  simp_rw [iteratedDeriv_const_mul_field]
  exact Matrix.det_mul_row c _

theorem wronskian_common_const {m : ℕ} (g : Fin m → ℂ → ℂ) (c z : ℂ) :
    wronskian (fun j w => c * g j w) z = c ^ m * wronskian g z := by
  simpa using wronskian_const_mul g (fun _ => c) z

/-- The forward direction of the classical Wronskian criterion, on an open set. -/
theorem wronskian_zero_of_linear_relation {m : ℕ} {g : Fin m → ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hg : ∀ j, DifferentiableOn ℂ (g j) U)
    (c : Fin m → ℂ) (hc : c ≠ 0) (hrel : ∀ z ∈ U, ∑ j, c j * g j z = 0)
    {z : ℂ} (hz : z ∈ U) : wronskian g z = 0 := by
  have hjet : ∀ i : Fin m, ∑ j, c j * iteratedDeriv (i : ℕ) (g j) z = 0 := by
    intro i
    have hzero : iteratedDeriv (i : ℕ) (fun w => ∑ j, c j * g j w) z = 0 := by
      have hEq : Set.EqOn (fun w => ∑ j, c j * g j w) (fun _ => 0) U := hrel
      simpa using hEq.iteratedDeriv_of_isOpen hU (i : ℕ) hz
    rw [iteratedDeriv_fun_sum] at hzero
    · simpa only [iteratedDeriv_const_mul_field] using hzero
    · intro j _
      have hd : ContDiffAt ℂ (i : ℕ) (g j) z :=
        ((hg j).analyticAt (hU.mem_nhds hz)).contDiffAt
      exact contDiffAt_const.mul hd
  by_contra hdet
  apply hc
  apply Matrix.eq_zero_of_mulVec_eq_zero (M := fun i j : Fin m => iteratedDeriv (i : ℕ) (g j) z) hdet
  funext i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using hjet i

theorem diskSupNorm_nonneg {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (Metric.closedBall 0 r)) : 0 ≤ diskSupNorm f r := by
  have hb := (isCompact_closedBall (0 : ℂ) r).bddAbove_image hf.norm
  have h0 : (0 : ℂ) ∈ Metric.closedBall 0 r := by simpa using hr
  exact (norm_nonneg _).trans (le_csSup hb (Set.mem_image_of_mem _ h0))

theorem diskSupNorm_mono {f : ℂ → ℂ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ContinuousOn f (Metric.closedBall 0 b)) : diskSupNorm f a ≤ diskSupNorm f b := by
  apply csSup_le
  · exact Set.Nonempty.image _ ⟨0, by simpa using ha⟩
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := hv
    exact le_csSup ((isCompact_closedBall (0 : ℂ) b).bddAbove_image hf.norm)
      (Set.mem_image_of_mem _ (Metric.closedBall_subset_closedBall hab hz))

theorem leastCombinationNorm_le_first (g : Fin 1 → ℂ → ℂ) {a : ℝ} (ha : 0 ≤ a)
    (hg : ∀ j, ContinuousOn (g j) (Metric.closedBall 0 a)) :
    leastCombinationNorm g a ≤ diskSupNorm (g 0) a := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro v hv
    obtain ⟨c, _hc, rfl⟩ := hv
    apply diskSupNorm_nonneg ha
    exact continuousOn_finsetSum _ (fun j _ => (hg j).const_mul (c j))
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · simp [coefficientNormSq]
    · simp

/-- The m=1 case of Proposition 2.2, with c=K=1. -/
theorem quantitativeWronskian_one (g : Fin 1 → ℂ → ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hg : ∀ j, ContinuousOn (g j) (Metric.closedBall 0 b)) :
    leastCombinationNorm g a ≤ diskSupNorm (wronskian g) b := by
  have h1 := leastCombinationNorm_le_first g ha
    (fun j => (hg j).mono (Metric.closedBall_subset_closedBall hab))
  have h2 := diskSupNorm_mono ha hab (hg 0)
  have heq : wronskian g = g 0 := funext (wronskian_one g)
  rw [heq]
  exact h1.trans h2

end ModifiedCartan
