import ModifiedCartan.CartanGrowthClosure
import ModifiedCartan.GrowthBootstrap
import ModifiedCartan.SmallPartitions

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

/-- Uniform inverse-Wronskian bounds on the genuine growth-controlled radii
force an absolute bound for the pair growth at the prescribed inner radius. -/
theorem pairGrowth_bounded_of_inverseWronskian_control {η r₀ A D : ℝ}
    (hη : 0 < η) (hηr : η < r₀) (hr1 : r₀ < 1) (hA : 0 ≤ A) (hD : 0 ≤ D) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Fin (m+1) → ℂ → ℂ),
      (∀ i, IsHolomorphicUnit (f i) (disk 1)) → (∀ z ∈ disk 1, ∑ i, f i z = 0) →
      (∀ i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧ -A ≤ Real.log ‖f i w/f j w‖) →
      (∃ w ∈ disk 1, normalizedWronskian (fun j : Fin m => f j.castSucc) w ≠ 0) →
      (∀ r ∈ Icc r₀ ((r₀+1)/2),
        r+1/pairGrowthMean f r ≤ (r₀+1)/2 →
        pairGrowthMean f (r+1/pairGrowthMean f r) ≤ 2*pairGrowthMean f r →
        proximityMean (fun z => (normalizedWronskian (fun j : Fin m => f j.castSucc) z)⁻¹) r ≤
          D*(Real.log (pairGrowthMean f r)+1)) →
      pairGrowthMean f r₀ ≤ C := by
  obtain ⟨B,hB,hclose⟩ := zero_sum_pairGrowth_bound_of_inverseWronskian hη hηr hr1 hA hD m
  let b := (r₀+1)/2
  have hrb : r₀ < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  obtain ⟨C,hC,hboot⟩ := growth_bound_from_large_radius_set (sub_pos.mpr hrb) B
  refine ⟨C,hC,?_⟩
  intro f hf hsum ha hN hinv
  have hsub : Icc r₀ b ⊆ Ico 0 1 := fun r hr =>
    ⟨hη.le.trans (hηr.le.trans hr.1),hr.2.trans_lt hb1⟩
  apply hboot (pairGrowthMean f) r₀ b (Icc r₀ b) hrb.le
    ((pairGrowthMean_continuousOn hf).mono hsub) ((pairGrowthMean_monotoneOn hf).mono hsub)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (pairGrowthMean_ge_one f r₀)) Subset.rfl
    (by simp [Real.volume_Icc])
  intro r hr hstep hgrowth
  have hM : 1 ≤ pairGrowthMean f r := pairGrowthMean_ge_one f r
  have hM0 : 0 < pairGrowthMean f r := by linarith
  have hgap : r+1/pairGrowthMean f r-r = 1/pairGrowthMean f r := by ring
  exact hclose f r (r+1/pairGrowthMean f r) (pairGrowthMean f r) hf hsum hr.1
    (lt_add_of_pos_right r (one_div_pos.mpr hM0)) (hstep.trans_lt hb1) hM hgap hgrowth ha hN
    (hinv r hr hstep hgrowth)

/-- Bounds on arbitrarily large interior circles give genuine local bounds
for every pairwise quotient on the entire unit disk. -/
theorem locallyBounded_quotients_of_pairGrowth_bounds {p : ℕ} {f : Family p} {η : ℝ}
    (hη : η < 1) (hf : UnitFamily f)
    (hb : ∀ R : ℝ, η < R → R < 1 → ∃ C : ℝ, ∀ n, pairGrowthMean (fun i => f i n) R ≤ C) :
    ∀ i j, LocallyBounded (fun n z => f i n z/f j n z) (disk 1) := by
  intro i j K hK hcK
  obtain ⟨a,⟨ha,ha1⟩,hKa⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1) hcK.isClosed hK
  let R := (max η a+1)/2
  have hmax : max η a < 1 := max_lt hη ha1
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hηR : η < R := by dsimp [R]; linarith [le_max_left η a]
  have haR : a < R := by dsimp [R]; linarith [le_max_right η a]
  obtain ⟨C,hC⟩ := hb R hηR hR1
  let Q := (R+a)/(R-a)
  have hQ : 0 ≤ Q := div_nonneg (by linarith) (by linarith)
  refine ⟨Real.exp (Q*C),?_⟩
  intro n z hz
  have hqu := unit_quotient (hf i n) (hf j n)
  have hza : ‖z‖ ≤ a := (by simpa using hKa hz : ‖z‖ < a).le
  have hh := norm_le_exp_proximity_on_closedBall ha.le haR
    (hqu.1.analyticOnNhd isOpen_ball |>.mono (closedBall_subset_ball hR1)) hza
  apply hh.trans
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    ((quotient_proximity_le_pairGrowthMean (fun k => f k n) i j R).trans (hC n)) hQ)

/-- The full-disk final branch, conditional only on the displayed analytic
inverse estimates. No extraction or local boundedness is supplied as a premise. -/
theorem cclass_univ_of_inverseWronskian_control {m : ℕ} {f : Family (m+1)} {η A : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hA : 0 ≤ A) (hf : UnitFamily f) (hs : ZeroSum f)
    (ha : ∀ n i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧ -A ≤ Real.log ‖f i n w/f j n w‖)
    (hN : ∀ n, ∃ w ∈ disk 1, normalizedWronskian (fun j : Fin m => f j.castSucc n) w ≠ 0)
    (hinv : ∀ r₀ : ℝ, η < r₀ → r₀ < 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      ∀ r ∈ Icc r₀ ((r₀+1)/2),
        r+1/pairGrowthMean (fun i => f i n) r ≤ (r₀+1)/2 →
        pairGrowthMean (fun i => f i n) (r+1/pairGrowthMean (fun i => f i n) r) ≤
          2*pairGrowthMean (fun i => f i n) r →
        proximityMean (fun z => (normalizedWronskian (fun j : Fin m => f j.castSucc n) z)⁻¹) r ≤
          D*(Real.log (pairGrowthMean (fun i => f i n) r)+1)) :
    IsCClass f Finset.univ (disk 1) := by
  have hb : ∀ R : ℝ, η < R → R < 1 → ∃ C : ℝ, ∀ n, pairGrowthMean (fun i => f i n) R ≤ C := by
    intro R hηR hR
    obtain ⟨D,hD,hi⟩ := hinv R hηR hR
    obtain ⟨C,hC,h⟩ := pairGrowth_bounded_of_inverseWronskian_control hη hηR hR hA hD m
    exact ⟨C,fun n => h (fun i => f i n) (fun i => hf i n) (hs n) (ha n) (hN n) (hi n)⟩
  exact cclass_univ_of_zeroSum Subset.rfl hs (Fin.last m)
    (fun j => locallyBounded_quotients_of_pairGrowth_bounds hη1 hf hb j (Fin.last m))

end ModifiedCartan
