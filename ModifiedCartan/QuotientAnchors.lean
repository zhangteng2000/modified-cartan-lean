import ModifiedCartan.CartanBoundedPairs
import ModifiedCartan.FiniteFailurePoints
import ModifiedCartan.QuotientGrowth
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

theorem diskSupNorm_ge_exp_of_log_anchor {f : ℂ → ℂ} {η A : ℝ}
    (hη : η < 1) (hf : IsHolomorphicUnit f (disk 1))
    (ha : ∃ w : ℂ, ‖w‖ ≤ η ∧ f w ≠ 0 ∧ -A ≤ Real.log ‖f w‖) :
    Real.exp (-A) ≤ diskSupNorm f η := by
  obtain ⟨w,hw,hn,hl⟩ := ha
  have hsup : ‖f w‖ ≤ diskSupNorm f η := le_csSup
    ((isCompact_closedBall (0 : ℂ) η).bddAbove_image
      (hf.1.continuousOn.mono (closedBall_subset_ball hη)).norm)
    (mem_image_of_mem (fun z => ‖f z‖) (by simpa using hw))
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (norm_pos_iff.mpr hn)] at he
  exact he.trans hsup

/-- Exclusion of every vanishing quotient subsequence constructs one common
inner disk and a uniform logarithmic anchor for every ordered pair. -/
theorem quotient_anchors_on_disk_of_no_vanishing {p : ℕ} {f : Family p} {T : ℝ}
    (hT : 0 < T) (hf : ∀ i n, IsHolomorphicUnit (f i n) (disk T)) (hno : NoVanishingQuotientSubsequence f (disk T)) :
    ∃ η A : ℝ, 0 < η ∧ η < T ∧ 0 ≤ A ∧ ∀ᶠ n in atTop, ∀ i j : Fin p,
      ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧ -A ≤ Real.log ‖f i n w/f j n w‖ := by
  let q : (Fin p × Fin p) → ℕ → ℂ → ℂ := fun ij n z => f ij.1 n z/f ij.2 n z
  have hq : ∀ ij n z, z ∈ disk T → q ij n z ≠ 0 :=
    fun ij n => (unit_quotient (hf ij.1 n) (hf ij.2 n)).2
  have hqn : ∀ ij, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence
      (fun n z => (q ij (φ n) z)⁻¹) (fun _ => 0) (disk T) := by
    intro ij hh
    apply hno ij.2 ij.1
    simpa only [q,inv_div] using hh
  obtain ⟨K,hK,hcK,A,hA,he⟩ := finite_unit_failure_points q isOpen_ball hq hqn
  obtain ⟨η,⟨hη,hη1⟩,hKη⟩ := exists_pos_lt_subset_ball hT hcK.isClosed hK
  refine ⟨η,A,hη,hη1,hA,?_⟩
  filter_upwards [he] with n hn
  intro i j
  obtain ⟨w,hw,hl⟩ := hn (j,i)
  have hnorm : ‖w‖ ≤ η := (by simpa using hKη hw : ‖w‖ < η).le
  have hi : f i n w/f j n w ≠ 0 := (unit_quotient (hf i n) (hf j n)).2 w (hK hw)
  have hlog : Real.log ‖f j n w/f i n w‖ = -Real.log ‖f i n w/f j n w‖ := by
    rw [show f j n w/f i n w = (f i n w/f j n w)⁻¹ by simp, norm_inv,Real.log_inv]
  change Real.log ‖f j n w/f i n w‖ ≤ A at hl
  rw [hlog] at hl
  exact ⟨w,hnorm,hi,by linarith⟩


theorem quotient_anchors_of_no_vanishing {p : ℕ} {f : Family p}
    (hf : UnitFamily f) (hno : NoVanishingQuotientSubsequence f (disk 1)) :
    ∃ η A : ℝ, 0 < η ∧ η < 1 ∧ 0 ≤ A ∧ ∀ᶠ n in atTop, ∀ i j : Fin p,
      ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧ -A ≤ Real.log ‖f i n w/f j n w‖ :=
  quotient_anchors_on_disk_of_no_vanishing (by norm_num) hf hno

end ModifiedCartan
