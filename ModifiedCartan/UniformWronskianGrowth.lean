import ModifiedCartan.NormalizedWronskianGrowth

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- One constant works for every selected Wronskian up to a fixed finite
order, after division by any common holomorphic unit. -/
theorem normalizedWronskian_bounded_order_growth_bound {η τ r₀ : ℝ}
    (hη : 0 < η) (hηr : η < r₀) (hτ : 0 < τ) (d : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : ℕ), m ≤ d →
      ∀ (g : Fin m → ℂ → ℂ) (h : ℂ → ℂ) (r R M : ℝ),
        (∀ j, IsHolomorphicUnit (g j) (disk 1)) → IsHolomorphicUnit h (disk 1) →
        (∀ j, τ ≤ diskSupNorm (fun z => g j z/h z) η) →
        r₀ ≤ r → r < R → R < 1 → 1 ≤ M → R-r = 1/M →
        (∀ j, proximityMean (fun z => g j z/h z) R ≤ 2*M) →
        proximityMean (normalizedWronskian g) r ≤ B*(Real.log M+1) := by
  classical
  have hb := fun k : Fin (d+1) => normalizedWronskian_growth_bound hη hηr hτ (k : ℕ)
  choose B hB hbound using hb
  refine ⟨∑ k, B k, Finset.sum_nonneg (fun k _ => hB k), ?_⟩
  intro m hm g h r R M hg hh ha hr hrR hR hM hgap hmean
  let k : Fin (d+1) := ⟨m,Nat.lt_succ_of_le hm⟩
  have hk : B k ≤ ∑ l, B l := Finset.single_le_sum (fun l _ => hB l) (Finset.mem_univ k)
  exact (hbound k g h r R M hg hh ha hr hrR hR hM hgap hmean).trans
    (mul_le_mul_of_nonneg_right hk (by linarith [Real.log_nonneg hM]))

end ModifiedCartan
