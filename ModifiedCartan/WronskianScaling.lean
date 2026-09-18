import ModifiedCartan.CombinationNorm
import ModifiedCartan.CombinationMinimum
import ModifiedCartan.CauchyBounds

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- Input scaling for every derivative jet needs analyticity only at the image point. -/
theorem analytic_iteratedDeriv_comp_mul {f : ℂ → ℂ} {c z : ℂ}
    (hf : AnalyticAt ℂ f (c * z)) (n : ℕ) :
    iteratedDeriv n (fun w => f (c * w)) z = c ^ n * iteratedDeriv n f (c * z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (fun w => f (c * w)) =ᶠ[𝓝 z]
        (fun w => c ^ n * iteratedDeriv n f (c * w)) := by
      have ht : Tendsto (fun w : ℂ => c * w) (𝓝 z) (𝓝 (c * z)) :=
        (continuous_const.mul continuous_id).continuousAt
      filter_upwards [ht.eventually hf.eventually_analyticAt] with w hw
      exact ih hw
    have hloc : AnalyticOnNhd ℂ f {c * z} := by
      intro w hw
      simpa only [mem_singleton_iff.mp hw] using hf
    have hd := (iteratedDeriv_analyticOnNhd hloc n (c * z) rfl).differentiableAt.hasDerivAt.comp z
      ((hasDerivAt_id z).const_mul c)
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hder := (hd.const_mul (c ^ n)).deriv
    simp only [Function.comp_def] at hder
    rw [hder, iteratedDeriv_succ, pow_succ]
    simp only [mul_one]
    ring

/-- Exact input-scaling exponent m(m-1)/2 in the Wronskian determinant. -/
theorem wronskian_comp_mul {m : ℕ} {g : Fin m → ℂ → ℂ} {c z : ℂ}
    (hg : ∀ j, AnalyticAt ℂ (g j) (c * z)) :
    wronskian (fun j w => g j (c * w)) z =
      c ^ (m * (m - 1) / 2) * wronskian g (c * z) := by
  unfold wronskian
  simp_rw [analytic_iteratedDeriv_comp_mul (hg _)]
  have he := Matrix.det_mul_column (fun i : Fin m => c ^ (i : ℕ))
    (.of fun i j => iteratedDeriv (i : ℕ) (g j) (c * z))
  simp only [Matrix.of_apply] at he
  rw [he]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  calc
    (∑ i : Fin m, (i : ℕ)) = ∑ i ∈ Finset.range m, i :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => i) m
    _ = _ := Finset.sum_range_id m

theorem real_scale_mem_closedBall {η r : ℝ} (hη : 0 < η) (z : ℂ) :
    (η : ℂ) * z ∈ closedBall (0 : ℂ) (η * r) ↔ z ∈ closedBall (0 : ℂ) r := by
  simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hη, mul_le_mul_iff_right₀ hη]

theorem diskSupNorm_input_scale (f : ℂ → ℂ) {η r : ℝ} (hη : 0 < η) :
    diskSupNorm (fun z => f ((η : ℂ) * z)) r = diskSupNorm f (η * r) := by
  unfold diskSupNorm
  congr 1
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(η : ℂ) * z, (real_scale_mem_closedBall hη z).mpr hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hηc : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
    refine ⟨z / (η : ℂ), ?_, ?_⟩
    · apply (real_scale_mem_closedBall hη _).mp
      simpa only [mul_div_cancel₀ _ hηc] using hz
    · simp only [mul_div_cancel₀ _ hηc]

theorem leastCombinationNorm_input_scale {m : ℕ} (g : Fin m → ℂ → ℂ)
    {η r : ℝ} (hη : 0 < η) :
    leastCombinationNorm (fun j z => g j ((η : ℂ) * z)) r =
      leastCombinationNorm g (η * r) := by
  unfold leastCombinationNorm
  congr 1
  ext v
  constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
  · rw [← diskSupNorm_input_scale (fun z => ∑ j, c j * g j z) hη]
    exact hv
  · rw [diskSupNorm_input_scale (fun z => ∑ j, c j * g j z) hη]
    exact hv

theorem leastCombinationNorm_const_mul {m : ℕ} (hm : 0 < m)
    {g : Fin m → ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r)) (a : ℂ) :
    leastCombinationNorm (fun j z => a * g j z) r = ‖a‖ * leastCombinationNorm g r := by
  obtain ⟨c, hc, hmin⟩ := leastCombinationNorm_attained hm hr hg
  have hgc : ∀ j, ContinuousOn (fun z => a * g j z) (closedBall (0 : ℂ) r) :=
    fun j => (hg j).const_mul a
  obtain ⟨d, hd, hmind⟩ := leastCombinationNorm_attained hm hr hgc
  have hscale : ∀ e : Fin m → ℂ,
      diskSupNorm (fun z => ∑ j, e j * (a * g j z)) r =
      ‖a‖ * diskSupNorm (fun z => ∑ j, e j * g j z) r := by
    intro e
    have he : (fun z => ∑ j, e j * (a * g j z)) =
        (fun z => a * ∑ j, e j * g j z) := by
      ext z
      simp only [Finset.mul_sum]
      congr 1
      ext j
      ring
    rw [he, diskSupNorm_const_mul hr
      (continuousOn_finsetSum _ (fun j _ => (hg j).const_mul (e j)))]
  apply le_antisymm
  · calc
      _ ≤ diskSupNorm (fun z => ∑ j, c j * (a * g j z)) r :=
        leastCombinationNorm_le hr hgc c hc
      _ = ‖a‖ * leastCombinationNorm g r := by rw [hscale, hmin]
  · rw [hmind, hscale]
    exact mul_le_mul_of_nonneg_left (leastCombinationNorm_le hr hg d hd) (norm_nonneg _)

end ModifiedCartan
