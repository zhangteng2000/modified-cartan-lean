import ModifiedCartan.LogDerivativeNormality
import ModifiedCartan.NormalizedParts

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

/-- A quotient converging to minus one gives an actual two-index C class. -/
theorem cclass_pair_of_ratio_neg_one {p : ℕ} {f : Family p} {U : Set ℂ}
    (hf : ∀ i n, IsHolomorphicUnit (f i n) U) {i j : Fin p} (hij : i ≠ j)
    (hlim : CompactConvergence (fun n z => f i n z / f j n z) (fun _ => -1) U) :
    IsCClass f {i, j} U := by
  have hb := compactConvergence_locallyBounded hlim
    (fun n => ((hf i n).1.div (hf j n).1 (hf j n).2).continuousOn)
  have hself : CompactConvergence (fun n z => f j n z / f j n z) (fun _ => (1 : ℂ)) U := by
    intro K hKU hK
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).tendstoUniformlyOn_const K |>.congr
    apply Eventually.of_forall
    intro n z hz
    exact (div_self ((hf j n).2 z (hKU hz))).symm
  refine ⟨j, by simp, ?_, ?_⟩
  · intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with hk | hk
    · subst k; exact hb
    · subst k; exact quotient_bounded_refl (fun n => (hf j n).2)
  · intro K hKU hK
    simpa only [sum_pair hij, Pi.add_def, neg_add_cancel] using (hlim K hKU hK).add (hself K hKU hK)

/-- Two overlapping cancelling pairs force a plus-one quotient limit. -/
theorem ratio_one_of_overlapping_cancellations {p : ℕ} {f : Family p} {U : Set ℂ}
    (hU : IsOpen U) (hf : ∀ i n, IsHolomorphicUnit (f i n) U) {i j k : Fin p}
    (hij : CompactConvergence (fun n z => f i n z / f j n z) (fun _ => -1) U)
    (hjk : CompactConvergence (fun n z => f j n z / f k n z) (fun _ => -1) U) :
    CompactConvergence (fun n z => f i n z / f k n z) (fun _ => 1) U := by
  have hh := ((compactConvergence_iff hU).mp hij).mul₀
    ((compactConvergence_iff hU).mp hjk) continuousOn_const continuousOn_const
  have hprod : CompactConvergence
      (fun n z => (f i n z / f j n z) * (f j n z / f k n z)) (fun _ => 1) U := by
    apply (compactConvergence_iff hU).mpr
    simpa only [Pi.mul_def, neg_mul_neg, one_mul] using hh
  apply compactConvergence_congr hprod
  intro n z hz
  field_simp [(hf j n).2 z hz]

/-- The bounded-logarithmic-derivative branch gives a nonzero finite ratio
limit under the two-sided no-decay alternative. -/
theorem ratio_unit_limit_of_logDerivative_bound {p : ℕ} {f : Family p} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hf : ∀ i n, IsHolomorphicUnit (f i n) (disk T))
    (i j : Fin p)
    (hb : ∀ n z, z ∈ disk T → ‖logDeriv (fun w => f i n w / f j n w) z‖ ≤ C)
    (hij : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => f i (φ n) z / f j (φ n) z) (fun _ => 0) (disk T))
    (hji : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => f j (φ n) z / f i (φ n) z) (fun _ => 0) (disk T)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ,
      IsHolomorphicUnit G (disk T) ∧
      CompactConvergence (fun n z => f i (φ n) z / f j (φ n) z) G (disk T) := by
  apply logDerivative_unit_limit_of_no_decay hT hC
    (fun n => ⟨(hf i n).1.div (hf j n).1 (hf j n).2,
      fun z hz => div_ne_zero ((hf i n).2 z hz) ((hf j n).2 z hz)⟩) hb
  · simpa only [Pi.div_apply, inv_div] using hji
  · exact hij

end ModifiedCartan
