import ModifiedCartan.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

def unitDiskExhaustionRadius (n : ℕ) : ℝ := 1-1/(n+2 : ℝ)

theorem unitDiskExhaustionRadius_pos (n : ℕ) : 0 < unitDiskExhaustionRadius n := by
  have hn : (1 : ℝ) < n+2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hn)

theorem unitDiskExhaustionRadius_lt_one (n : ℕ) : unitDiskExhaustionRadius n < 1 := by
  exact sub_lt_self 1 (one_div_pos.mpr (by positivity))

theorem unitDiskExhaustion_compact_cover (K : Set ℂ) (hK : K ⊆ disk 1) (hcK : IsCompact K) :
    ∃ N : ℕ, ∀ n, N ≤ n → K ⊆ disk (unitDiskExhaustionRadius n) := by
  obtain ⟨a,⟨_,ha1⟩,hKa⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1) hcK.isClosed hK
  have hseq : Tendsto (fun n : ℕ => 1/(n+2 : ℝ)) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hh
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hseq.eventually (gt_mem_nhds (sub_pos.mpr ha1)))
  refine ⟨N,?_⟩
  intro n hn z hz
  have hza : ‖z‖ < a := by simpa using hKa hz
  have hh := hN n hn
  have hzR : ‖z‖ < unitDiskExhaustionRadius n := by dsimp [unitDiskExhaustionRadius]; linarith
  simpa [disk] using hzR

end ModifiedCartan
