import ModifiedCartan.FiveExampleLimits
import ModifiedCartan.PartitionObstruction

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real Filter Topology
namespace ModifiedCartan

/-- The five functions in eq:five-counterexample, with n+1 so every natural
sequence index uses a positive integer parameter. -/
def fiveCounterexample : Family 5 := fun i n z =>
  ![fiveA ((n : ℝ) + 1) z,
    fiveA ((n : ℝ) + 1) (-z),
    fivea ((n : ℝ) + 1) z - fiveA ((n : ℝ) + 1) z,
    fivea ((n : ℝ) + 1) (-z) - fiveA ((n : ℝ) + 1) (-z),
    -1] i

theorem holomorphicUnit_neg_input {f : ℂ → ℂ} (hf : IsHolomorphicUnit f (disk 1)) :
    IsHolomorphicUnit (fun z => f (-z)) (disk 1) := by
  have hmap : MapsTo (fun z : ℂ => -z) (disk 1) (disk 1) := by
    intro z hz
    simpa [disk] using hz
  exact ⟨hf.1.comp differentiable_neg.differentiableOn hmap,
    fun z hz => hf.2 _ (hmap hz)⟩

theorem fiveCounterexample_units : UnitFamily fiveCounterexample := by
  intro i n
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hN0 : 0 < (n : ℝ) + 1 := by positivity
  fin_cases i
  · exact fiveA_unit hN0
  · exact holomorphicUnit_neg_input (fiveA_unit hN0)
  · exact fivea_sub_fiveA_unit hN
  · exact holomorphicUnit_neg_input (fivea_sub_fiveA_unit hN)
  · exact ⟨differentiableOn_const _, fun _ _ => by norm_num [fiveCounterexample]⟩

theorem fiveCounterexample_zeroSum : ZeroSum fiveCounterexample := by
  intro n z _hz
  simp only [fiveCounterexample, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  linear_combination fivea_complement ((n : ℝ) + 1) z

theorem fiveCounterexample_grows_at_zero (j : Fin 5) (hj : j ≠ 4) :
    Tendsto (fun n : ℕ => ‖fiveCounterexample j n 0‖) atTop atTop := by
  fin_cases j
  · exact fiveA_grows_at_zero
  · simpa [fiveCounterexample] using fiveA_grows_at_zero
  · exact fivea_sub_fiveA_grows_at_zero
  · simpa [fiveCounterexample] using fivea_sub_fiveA_grows_at_zero
  · exact (hj rfl).elim

theorem fiveCounterexample_vanishing_points {R : ℝ} (hR : sharpRadius < R) (hR1 : R ≤ 1)
    (j : Fin 5) (hj : j ≠ 4) :
    ∃ z ∈ disk R, Tendsto (fun n : ℕ => fiveCounterexample j n z) atTop (𝓝 0) := by
  obtain ⟨t, htr, htR⟩ := exists_between hR
  have ht0 := sharpRadius_pos.trans htr
  have ht1 := htR.trans_le hR1
  have hminus : ((-t : ℝ) : ℂ) ∈ disk R := by simpa [disk, abs_of_pos ht0] using htR
  have hplus : (t : ℂ) ∈ disk R := by simpa [disk, abs_of_pos ht0] using htR
  fin_cases j
  · exact ⟨_, hminus, fiveA_vanishes_negative_point htr ht1⟩
  · refine ⟨_, hplus, ?_⟩
    simpa [fiveCounterexample] using fiveA_vanishes_negative_point htr ht1
  · exact ⟨_, hminus, fivea_sub_fiveA_vanishes_negative_point htr ht1⟩
  · refine ⟨_, hplus, ?_⟩
    simpa [fiveCounterexample] using fivea_sub_fiveA_vanishes_negative_point htr ht1
  · exact (hj rfl).elim

/-- The explicit manuscript counterexample has no C-class partition after any
subsequence on any allowed disk larger than 2-sqrt(3). -/
theorem fiveCounterexample_no_partition {R : ℝ} (hR : sharpRadius < R) (hR1 : R ≤ 1)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ¬ Nonempty (CPartition (subsequence fiveCounterexample φ) (disk R)) := by
  have hU1 : disk R ⊆ disk 1 := ball_subset_ball hR1
  exact constant_coordinate_partition_obstruction
    (fun i n z hz => (fiveCounterexample_units i n).2 z (hU1 hz)) (4 : Fin 5)
    (show (0 : ℂ) ∈ disk R from mem_ball_self (sharpRadius_pos.trans hR))
    (fun _ _ _ => rfl) fiveCounterexample_grows_at_zero
    (fiveCounterexample_vanishing_points hR hR1) hφ

theorem not_partitionProperty_five_above_sharpRadius {R : ℝ}
    (hR : sharpRadius < R) (hR1 : R ≤ 1) : ¬ PartitionProperty 5 (disk R) := by
  intro h
  obtain ⟨φ, hφ, hP⟩ := h fiveCounterexample fiveCounterexample_units fiveCounterexample_zeroSum
  exact fiveCounterexample_no_partition hR hR1 hφ hP

end ModifiedCartan
