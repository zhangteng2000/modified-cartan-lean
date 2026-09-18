import ModifiedCartan.Wronskian

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

theorem diskSupNorm_attained {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall (0 : ℂ) r)) :
    ∃ z ∈ closedBall (0 : ℂ) r, diskSupNorm f r = ‖f z‖ := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn
    ⟨0, by simp [hr]⟩ hf.norm
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · exact csSup_le (Nonempty.image _ ⟨z, hz⟩) (by rintro v ⟨w, hw, rfl⟩; exact hmax hw)
  · exact le_csSup ((isCompact_closedBall (0 : ℂ) r).bddAbove_image hf.norm) (mem_image_of_mem _ hz)

theorem diskSupNorm_const_mul {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn f (closedBall (0 : ℂ) r)) (a : ℂ) :
    diskSupNorm (fun z => a * f z) r = ‖a‖ * diskSupNorm f r := by
  obtain ⟨z, hz, hmax⟩ := diskSupNorm_attained hr hf
  rw [hmax]
  have hb := (isCompact_closedBall (0 : ℂ) r).bddAbove_image hf.norm
  apply le_antisymm
  · apply csSup_le (Nonempty.image _ ⟨z, hz⟩)
    rintro v ⟨w, hw, rfl⟩
    change ‖a * f w‖ ≤ ‖a‖ * ‖f z‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← hmax]
    exact le_csSup hb (mem_image_of_mem _ hw)
  · have hs := le_csSup ((isCompact_closedBall (0 : ℂ) r).bddAbove_image
      (continuousOn_const.mul hf).norm) (mem_image_of_mem (fun w => ‖a * f w‖) hz)
    change ‖a * f z‖ ≤ diskSupNorm (fun z => a * f z) r at hs
    simpa only [norm_mul] using hs

theorem coefficientNormSq_single {m : ℕ} (k : Fin m) :
    coefficientNormSq (Pi.single k (1 : ℂ)) = 1 := by
  classical
  unfold coefficientNormSq
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    simp [hjk]
  · simp

theorem coefficientNormSq_const_mul {m : ℕ} (c : Fin m → ℂ) (a : ℂ) :
    coefficientNormSq (fun j => a * c j) = ‖a‖ ^ 2 * coefficientNormSq c := by
  simp only [coefficientNormSq, norm_mul, mul_pow, Finset.mul_sum]

theorem coefficientNormSq_nonneg {m : ℕ} (c : Fin m → ℂ) : 0 ≤ coefficientNormSq c :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem leastCombination_values_bddBelow {m : ℕ} {g : Fin m → ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r)) :
    BddBelow {v : ℝ | ∃ c : Fin m → ℂ, coefficientNormSq c = 1 ∧
      v = diskSupNorm (fun z => ∑ j, c j * g j z) r} := by
  refine ⟨0, ?_⟩
  rintro v ⟨c, _, rfl⟩
  exact diskSupNorm_nonneg hr (continuousOn_finsetSum _ (fun j _ => (hg j).const_mul (c j)))

theorem leastCombinationNorm_le {m : ℕ} {g : Fin m → ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r))
    (c : Fin m → ℂ) (hc : coefficientNormSq c = 1) :
    leastCombinationNorm g r ≤ diskSupNorm (fun z => ∑ j, c j * g j z) r :=
  csInf_le (leastCombination_values_bddBelow hr hg) ⟨c, hc, rfl⟩

theorem leastCombinationNorm_le_coordinate {m : ℕ} {g : Fin m → ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r)) (k : Fin m) :
    leastCombinationNorm g r ≤ diskSupNorm (g k) r := by
  classical
  simpa [Pi.single_apply] using leastCombinationNorm_le hr hg _ (coefficientNormSq_single k)

theorem leastCombinationNorm_nonneg {m : ℕ} {g : Fin m → ℂ → ℂ} {r : ℝ}
    (hm : 0 < m) (hr : 0 ≤ r) (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r)) :
    0 ≤ leastCombinationNorm g r := by
  let k : Fin m := ⟨0, hm⟩
  apply le_csInf
  · exact ⟨_, Pi.single k 1, coefficientNormSq_single k, rfl⟩
  · rintro v ⟨c, _, rfl⟩
    exact diskSupNorm_nonneg hr (continuousOn_finsetSum _ (fun j _ => (hg j).const_mul (c j)))

theorem leastCombinationNorm_le_one {m : ℕ} {g : Fin m → ℂ → ℂ} {r : ℝ}
    (hm : 0 < m) (hr : 0 ≤ r) (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r))
    (hbound : ∀ j z, z ∈ closedBall (0 : ℂ) r → ‖g j z‖ ≤ 1) :
    leastCombinationNorm g r ≤ 1 := by
  let k : Fin m := ⟨0, hm⟩
  apply (leastCombinationNorm_le_coordinate hr hg k).trans
  exact csSup_le (Nonempty.image _ ⟨0, by simp [hr]⟩)
    (by rintro v ⟨z, hz, rfl⟩; exact hbound k z hz)

/-- A coefficient vector whose Euclidean norm is at least one gives a combination
whose supremum norm is at least Λ. This is the normalization used in the induction. -/
theorem leastCombinationNorm_le_unnormalized {m : ℕ} {g : Fin m → ℂ → ℂ} {r : ℝ}
    (hm : 0 < m) (hr : 0 ≤ r) (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r))
    (c : Fin m → ℂ) (hc : 1 ≤ coefficientNormSq c) :
    leastCombinationNorm g r ≤ diskSupNorm (fun z => ∑ j, c j * g j z) r := by
  let C := Real.sqrt (coefficientNormSq c)
  have hC : 0 < C := Real.sqrt_pos.mpr (by linarith)
  have hC2 : C ^ 2 = coefficientNormSq c := Real.sq_sqrt (coefficientNormSq_nonneg c)
  have hC1 : 1 ≤ C := by nlinarith
  let d : Fin m → ℂ := fun j => (C : ℂ)⁻¹ * c j
  have hd : coefficientNormSq d = 1 := by
    rw [coefficientNormSq_const_mul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    rw [← hC2, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hC.ne')]
  have ht := leastCombinationNorm_le hr hg d hd
  have he : (fun z => ∑ j, d j * g j z) =
      (fun z => (C : ℂ)⁻¹ * ∑ j, c j * g j z) := by
    ext z
    simp [d, Finset.mul_sum, mul_assoc]
  rw [he, diskSupNorm_const_mul hr (continuousOn_finsetSum _ (fun j _ => (hg j).const_mul (c j)))] at ht
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC] at ht
  have hmul := mul_le_mul_of_nonneg_left ht hC.le
  rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at hmul
  have ht0 := leastCombinationNorm_nonneg hm hr hg
  exact (le_mul_of_one_le_left ht0 hC1).trans hmul

/-- Removing the last function can only increase the least normalized combination norm. -/
theorem leastCombinationNorm_initial_subfamily {m : ℕ} (hm : 0 < m)
    {g : Fin (m + 1) → ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r)) :
    leastCombinationNorm g r ≤ leastCombinationNorm (fun j : Fin m => g j.castSucc) r := by
  classical
  let k : Fin m := ⟨0, hm⟩
  apply le_csInf
  · exact ⟨_, Pi.single k 1, coefficientNormSq_single k, rfl⟩
  · rintro v ⟨c, hc, rfl⟩
    let d : Fin (m + 1) → ℂ := Fin.snoc c 0
    have hd : coefficientNormSq d = 1 := by
      simpa [coefficientNormSq, d, Fin.sum_univ_castSucc] using hc
    have h := leastCombinationNorm_le hr hg d hd
    simpa [d, Fin.sum_univ_castSucc] using h

end ModifiedCartan
