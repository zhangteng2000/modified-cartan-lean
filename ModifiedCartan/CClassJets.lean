import ModifiedCartan.PartitionTheorem

noncomputable section
set_option autoImplicit false
open Filter Topology Set Metric
namespace ModifiedCartan

theorem locallyBounded_deriv_zero {g : ℕ → ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : ∀ n, DifferentiableOn ℂ (g n) (disk r)) (hb : LocallyBounded g (disk r)) :
    ∃ C : ℝ, ∀ n, ‖deriv (g n) 0‖ ≤ C := by
  have hsub : closedBall (0 : ℂ) (r / 2) ⊆ disk r := closedBall_subset_ball (by linarith)
  obtain ⟨C, hC⟩ := hb (closedBall (0 : ℂ) (r / 2)) hsub (isCompact_closedBall ..)
  refine ⟨C / (r / 2), ?_⟩
  intro n
  have hd : DifferentiableOn ℂ (g n) (closure (ball 0 (r / 2))) := by
    rw [closure_ball _ (by linarith : r / 2 ≠ 0)]
    exact (hg n).mono hsub
  have he := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
    (by linarith : 0 < r / 2) hd.diffContOnCl
    (fun z hz => hC n z (sphere_subset_closedBall hz))
  simpa using he

theorem tendsto_div_real_atTop_zero_of_bounded {u : ℕ → ℂ} {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) (htpos : ∀ n, 0 < t n)
    (hb : ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C) :
    Tendsto (fun n => u n / (t n : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hb
  have hlim : Tendsto (fun n => C * (t n)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ht)
  apply squeeze_zero_norm (fun n => ?_) hlim
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hC n) (inv_nonneg.mpr (htpos n).le)

/-- A C-class forces both cancellation of limiting values and equality of the
limiting logarithmic derivative rates. Base points may vary along the sequence. -/
theorem cclass_jet_limits {p : ℕ} {f : Family p} {I : Finset (Fin p)} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hf : UnitFamily f) (hI : IsCClass f I (disk r))
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) (htpos : ∀ n, 0 < t n)
    (c d : Fin p → ℂ) (hc : ∀ i, c i ≠ 0)
    (hcenter : ∀ i, Tendsto (fun n => f i n 0) atTop (𝓝 (c i)))
    (hder : ∀ i, Tendsto (fun n => deriv (f i n) 0 / (t n : ℂ)) atTop (𝓝 (d i))) :
    (∑ i ∈ I, c i = 0) ∧ ∃ k ∈ I, ∀ i ∈ I, d i / c i = d k / c k := by
  classical
  obtain ⟨k, hk, hb, hsum⟩ := hI
  have hz : (0 : ℂ) ∈ disk r := by simpa [disk] using hr
  have hz1 : (0 : ℂ) ∈ disk 1 := by simp [disk]
  have hsumlim := tendsto_finsetSum I (fun i _ => (hcenter i).div (hcenter k) (hc k))
  have hsumzero : ∑ i ∈ I, c i / c k = 0 :=
    tendsto_nhds_unique hsumlim (compactConvergence_pointwise hsum hz)
  have hcanc : ∑ i ∈ I, c i = 0 := by
    rw [← Finset.sum_div] at hsumzero
    exact (div_eq_zero_iff).mp hsumzero |>.resolve_right (hc k)
  refine ⟨hcanc, k, hk, ?_⟩
  intro i hi
  let q : ℕ → ℂ → ℂ := fun n z => f i n z / f k n z
  have hq : ∀ n, DifferentiableOn ℂ (q n) (disk r) := fun n =>
    ((hf i n).1.div (hf k n).1 (hf k n).2).mono (ball_subset_ball hr1)
  have hqbound := locallyBounded_deriv_zero hr hq (hb i hi)
  have hzero := tendsto_div_real_atTop_zero_of_bounded ht htpos hqbound
  have hqeq : ∀ n, deriv (q n) 0 / (t n : ℂ) =
      ((deriv (f i n) 0 / (t n : ℂ)) * f k n 0 -
        f i n 0 * (deriv (f k n) 0 / (t n : ℂ))) / (f k n 0) ^ 2 := by
    intro n
    have hdi := ((hf i n).1.differentiableAt (isOpen_ball.mem_nhds hz1)).hasDerivAt
    have hdk := ((hf k n).1.differentiableAt (isOpen_ball.mem_nhds hz1)).hasDerivAt
    have he := (hdi.div hdk ((hf k n).2 0 hz1)).deriv
    simp only [Pi.div_def] at he
    change deriv (fun z => f i n z / f k n z) 0 / (t n : ℂ) = _
    rw [he]
    ring
  have hratelim : Tendsto (fun n => deriv (q n) 0 / (t n : ℂ)) atTop
      (𝓝 ((d i * c k - c i * d k) / (c k) ^ 2)) := by
    simp only [hqeq]
    exact (((hder i).mul (hcenter k)).sub ((hcenter i).mul (hder k))).div
      ((hcenter k).pow 2) (pow_ne_zero _ (hc k))
  have heq : (d i * c k - c i * d k) / (c k) ^ 2 = 0 := tendsto_nhds_unique hratelim hzero
  have heq' : d i * c k - c i * d k = 0 :=
    (div_eq_zero_iff.mp heq).resolve_right (pow_ne_zero _ (hc k))
  apply (div_eq_div_iff (hc i) (hc k)).mpr
  linear_combination heq'

end ModifiedCartan
