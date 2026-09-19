import ModifiedCartan.FiveCounterexample
import ModifiedCartan.FiveOptimalityUpper

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real Filter Topology
namespace ModifiedCartan

theorem five_ratio_compactConvergence :
    CompactConvergence (fun n z => fivea ((n : ℝ) + 1) z / fiveA ((n : ℝ) + 1) z)
      (fun _ => 0) (disk 1) := by
  have hl : Tendsto (fun n : ℕ => 3 / (4 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have hh := (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)).const_mul (3 / 4 : ℝ)
    simpa only [Function.comp_def, mul_zero, zero_mul, div_eq_mul_inv, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm] using hh
  intro K hK _hcompact
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hl.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  simpa only [dist_zero_left] using
    (fivea_div_fiveA_bound (show 0 < (n : ℝ) + 1 by positivity) (hK hz)).trans_lt hn

theorem zero_limit_excludes_reciprocal_zero_limit {u : ℕ → ℂ}
    (hu : ∀ n, u n ≠ 0) (hlim : Tendsto u atTop (𝓝 0)) :
    ¬ Tendsto (fun n => (u n)⁻¹) atTop (𝓝 0) := by
  intro hi
  have hh := hlim.mul hi
  simp only [mul_zero] at hh
  have he : (fun n => u n * (u n)⁻¹) = fun _ => (1 : ℂ) := funext (fun n => mul_inv_cancel₀ (hu n))
  rw [he] at hh
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hh)

set_option maxHeartbeats 800000 in
/-- The same explicit pair proves that the sharp two-term absorption radius
cannot be increased, even when the summed numerators are identically one. -/
theorem not_absorption_two_above_sharpRadius {R : ℝ} (hR : sharpRadius < R) (hR1 : R ≤ 1) :
    ¬ AbsorptionAt 2 (disk R) := by
  let A : Family 2 := fun i n z => ![fiveA ((n : ℝ) + 1) z, fiveA ((n : ℝ) + 1) (-z)] i
  let a : Family 2 := fun i n z => ![fivea ((n : ℝ) + 1) z, fivea ((n : ℝ) + 1) (-z)] i
  have hA : UnitFamily A := by
    intro i n
    fin_cases i
    · exact fiveA_unit (by positivity)
    · exact holomorphicUnit_neg_input (fiveA_unit (by positivity))
  have ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1) := by
    intro i n
    fin_cases i
    · exact fivea_differentiable _
    · exact (fivea_differentiable _).comp differentiable_neg.differentiableOn
        (by intro z hz; simpa [disk] using hz)
  have hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) (fun _ => 0) (disk 1) := by
    intro i
    fin_cases i
    · exact five_ratio_compactConvergence
    · intro K hK hcompact
      have hneg : (fun z : ℂ => -z) '' K ⊆ disk 1 := by
        rintro z ⟨w, hw, rfl⟩
        simpa [disk] using hK hw
      exact ((five_ratio_compactConvergence _ hneg (hcompact.image continuous_neg)).comp
        (fun z : ℂ => -z)).mono (fun z hz => mem_image_of_mem _ hz)
  have hsum : CompactConvergence (fun n z => ∑ i, a i n z) (fun _ => 1) (disk 1) := by
    have he : (fun n z => ∑ i, a i n z) = fun (_ : ℕ) (_ : ℂ) => (1 : ℂ) := by
      funext n z
      simpa only [a, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
        fivea_complement ((n : ℝ) + 1) z
    rw [he]
    intro K _ _
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).tendstoUniformlyOn_const K
  intro h
  obtain ⟨i, φ, hφ, hrec⟩ := h A a (fun _ => 1) hA ha hsmall hsum
    ⟨0, mem_ball_self (by norm_num), one_ne_zero⟩
  obtain ⟨t, htr, htR⟩ := exists_between hR
  have ht0 := sharpRadius_pos.trans htr
  have ht1 := htR.trans_le hR1
  have htneg : ((-t : ℝ) : ℂ) ∈ disk R := by simpa [disk, abs_of_pos ht0] using htR
  have htpos : (t : ℂ) ∈ disk R := by simpa [disk, abs_of_pos ht0] using htR
  have hvan := (fiveA_vanishes_negative_point htr ht1).comp hφ.tendsto_atTop
  have hne (n : ℕ) : fiveA ((φ n : ℝ) + 1) ((-t : ℝ) : ℂ) ≠ 0 :=
    (fiveA_unit (by positivity)).2 _ (ball_subset_ball hR1 htneg)
  fin_cases i
  · exact zero_limit_excludes_reciprocal_zero_limit hne hvan (compactConvergence_pointwise hrec htneg)
  · apply zero_limit_excludes_reciprocal_zero_limit hne hvan
    simpa [A] using compactConvergence_pointwise hrec htpos

theorem two_absorption_diameter_cannot_increase {d : ℝ} (hd : Real.log 3 < d) :
    ∃ U : Set ℂ, U.Nonempty ∧ IsOpen U ∧ U ⊆ disk 1 ∧
      HasHyperbolicDiameterLE U d ∧ ¬ AbsorptionAt 2 U := by
  obtain ⟨R, hR, hR1, hdiam⟩ := exists_disk_above_sharp_below_diameter hd
  exact ⟨disk R, ⟨0, mem_ball_self (sharpRadius_pos.trans hR)⟩, isOpen_ball,
    ball_subset_ball hR1.le, hdiam, not_absorption_two_above_sharpRadius hR hR1.le⟩

end ModifiedCartan
