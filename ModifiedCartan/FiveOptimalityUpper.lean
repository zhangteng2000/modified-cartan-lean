import ModifiedCartan.FiveCounterexample
import ModifiedCartan.PartitionTheorem

noncomputable section
set_option autoImplicit false
open Complex Metric Set Real Filter Topology
namespace ModifiedCartan

theorem optimalFiveRadius_le_sharpRadius : optimalRadius 5 ≤ sharpRadius := by
  obtain ⟨ε, hε, hε1, hP⟩ := partitionTheorem_proved 5 (by norm_num)
  apply csSup_le (show {r : ℝ | 0 < r ∧ r < 1 ∧ PartitionProperty 5 (disk r)}.Nonempty from
    ⟨ε, hε, hε1, hP⟩)
  intro r hr
  by_contra hh
  exact not_partitionProperty_five_above_sharpRadius (lt_of_not_ge hh) hr.2.1.le hr.2.2

theorem exists_disk_above_sharp_below_diameter {d : ℝ} (hd : Real.log 3 < d) :
    ∃ R : ℝ, sharpRadius < R ∧ R < 1 ∧ HasHyperbolicDiameterLE (disk R) d := by
  have hr : |sharpRadius| < 1 := by simpa [abs_of_pos sharpRadius_pos] using sharpRadius_lt_one
  have hc := (hyperbolicRadialCoordinate_continuousAt hr).const_mul 2
  have hv : 2 * hyperbolicRadialCoordinate sharpRadius = Real.log 3 := sharpRadius_log_diameter
  have ht := hc.tendsto
  rw [hv] at ht
  have he : ∀ᶠ R : ℝ in 𝓝[>] sharpRadius,
      sharpRadius < R ∧ R < 1 ∧ 2 * hyperbolicRadialCoordinate R < d := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds sharpRadius_lt_one).filter_mono nhdsWithin_le_nhds,
      (ht.eventually (gt_mem_nhds hd)).filter_mono nhdsWithin_le_nhds] with R hR hR1 hRd
    exact ⟨hR, hR1, hRd⟩
  obtain ⟨R, hR, hR1, hRd⟩ := he.exists
  exact ⟨R, hR, hR1, (disk_hyperbolicDiameter_iff (sharpRadius_pos.trans hR) hR1).mpr hRd.le⟩

/-- No larger universal hyperbolic diameter can satisfy the five-function
partition conclusion, even on a connected round disk. -/
theorem five_partition_diameter_cannot_increase {d : ℝ} (hd : Real.log 3 < d) :
    ∃ U : Set ℂ, U.Nonempty ∧ IsOpen U ∧ U ⊆ disk 1 ∧
      HasHyperbolicDiameterLE U d ∧ ¬ PartitionProperty 5 U := by
  obtain ⟨R, hR, hR1, hdiam⟩ := exists_disk_above_sharp_below_diameter hd
  exact ⟨disk R, ⟨0, mem_ball_self (sharpRadius_pos.trans hR)⟩, isOpen_ball,
    ball_subset_ball hR1.le, hdiam, not_partitionProperty_five_above_sharpRadius hR hR1.le⟩

end ModifiedCartan
