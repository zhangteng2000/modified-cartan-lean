import ModifiedCartan.UnitGrowth
import ModifiedCartan.ProximityLocal

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

theorem maxWithZero_unit (x : ℝ) : maxWithZero (fun _ : Unit => x) = max 0 x := by
  apply le_antisymm
  · exact maxWithZero_le (le_max_left _ _) (fun _ => le_max_right _ _)
  · exact max_le (maxWithZero_nonneg _) (le_maxWithZero (fun _ : Unit => x) ())

theorem proximityMean_eq_harmonicGrowthMean (f : ℂ → ℂ) :
    proximityMean f = harmonicGrowthMean (fun _ : Unit => fun z => Real.log ‖f z‖) := by
  ext r
  simp only [proximityMean,ValueDistribution.proximity_top,harmonicGrowthMean,maxWithZero_unit,Real.posLog_apply]

theorem unit_proximityMean_continuousOn {f : ℂ → ℂ} (hf : IsHolomorphicUnit f (disk 1)) :
    ContinuousOn (proximityMean f) (Ico 0 1) := by
  rw [proximityMean_eq_harmonicGrowthMean]
  exact harmonicGrowthMean_continuousOn (fun _ => unit_log_harmonic hf)

theorem unit_proximityMean_monotoneOn {f : ℂ → ℂ} (hf : IsHolomorphicUnit f (disk 1)) :
    MonotoneOn (proximityMean f) (Ico 0 1) := by
  rw [proximityMean_eq_harmonicGrowthMean]
  exact harmonicGrowthMean_monotoneOn (fun _ => unit_log_harmonic hf)

def pairGrowthMean {p : ℕ} (g : Fin p → ℂ → ℂ) (r : ℝ) : ℝ :=
  1 + ∑ i, ∑ j, proximityMean (fun z => g i z/g j z) r

theorem pairGrowthMean_ge_one {p : ℕ} (g : Fin p → ℂ → ℂ) (r : ℝ) :
    1 ≤ pairGrowthMean g r := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => ValueDistribution.proximity_nonneg r))

theorem unit_quotient {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : IsHolomorphicUnit f U) (hg : IsHolomorphicUnit g U) :
    IsHolomorphicUnit (fun z => f z/g z) U :=
  ⟨hf.1.div hg.1 hg.2,fun z hz => div_ne_zero (hf.2 z hz) (hg.2 z hz)⟩

theorem pairGrowthMean_continuousOn {p : ℕ} {g : Fin p → ℂ → ℂ}
    (hg : ∀ j, IsHolomorphicUnit (g j) (disk 1)) :
    ContinuousOn (pairGrowthMean g) (Ico 0 1) := by
  apply ContinuousOn.add continuousOn_const
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_finsetSum
  intro j hj
  exact unit_proximityMean_continuousOn (unit_quotient (hg i) (hg j))

theorem pairGrowthMean_monotoneOn {p : ℕ} {g : Fin p → ℂ → ℂ}
    (hg : ∀ j, IsHolomorphicUnit (g j) (disk 1)) :
    MonotoneOn (pairGrowthMean g) (Ico 0 1) := by
  intro r hr R hR hrR
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact unit_proximityMean_monotoneOn (unit_quotient (hg i) (hg j)) hr hR hrR

theorem quotient_proximity_le_pairGrowthMean {p : ℕ} (g : Fin p → ℂ → ℂ) (i j : Fin p) (r : ℝ) :
    proximityMean (fun z => g i z/g j z) r ≤ pairGrowthMean g r := by
  have h1 : proximityMean (fun z => g i z/g j z) r ≤ ∑ k, proximityMean (fun z => g i z/g k z) r :=
    Finset.single_le_sum (f := fun k : Fin p => proximityMean (fun z => g i z/g k z) r) (fun _ _ => ValueDistribution.proximity_nonneg r) (Finset.mem_univ j)
  have h2 : (∑ k, proximityMean (fun z => g i z/g k z) r) ≤
      ∑ l, ∑ k, proximityMean (fun z => g l z/g k z) r :=
    Finset.single_le_sum (f := fun l : Fin p => ∑ k, proximityMean (fun z => g l z/g k z) r) (fun _ _ => Finset.sum_nonneg (fun _ _ => ValueDistribution.proximity_nonneg r))
      (Finset.mem_univ i)
  exact (h1.trans h2).trans (le_add_of_nonneg_left (by norm_num))

end ModifiedCartan
