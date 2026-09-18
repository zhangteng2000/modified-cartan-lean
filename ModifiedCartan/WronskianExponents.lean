import ModifiedCartan.QuantitativeWronskian
import ModifiedCartan.AnalyticStatements

noncomputable section
set_option autoImplicit false
open Metric
namespace ModifiedCartan

/-- Produce the manuscript's exponent sequence, including its prescribed K₁ = 1. -/
theorem exists_wronskianExponents : ∃ K : ℕ → ℝ,
    K 0 = 0 ∧ K 1 = 1 ∧ WronskianExponents K ∧ ∀ m : ℕ, (m : ℝ) ≤ K m := by
  classical
  have hex := fun n : ℕ => quantitativeWronskian_proved (n + 2) (by omega)
    (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  choose c K hc hK hbound using hex
  let L : ℕ → ℝ := fun m => if m = 0 then 0 else if m = 1 then 1 else K (m - 2)
  have hL0 : L 0 = 0 := by simp [L]
  have hL1 : L 1 = 1 := by simp [L]
  have hLge : ∀ m : ℕ, (m : ℝ) ≤ L m := by
    intro m
    rcases m with _ | (_ | n)
    · simp [hL0]
    · simp [hL1]
    · simpa [L, Nat.add_assoc] using hK n
  refine ⟨L, hL0, hL1, ?_, hLge⟩
  intro m hm
  refine ⟨hLge m, ?_⟩
  rcases m with _ | (_ | n)
  · omega
  · refine ⟨1, by norm_num, ?_⟩
    intro g hg _hbound
    rw [hL1, Real.rpow_one, one_mul]
    exact quantitativeWronskian_one g (by norm_num) (by norm_num)
      (fun j => (hg j).continuousOn.mono (closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1)))
  · refine ⟨c n, hc n, ?_⟩
    intro g hg hb
    simpa [L, Nat.add_assoc] using hbound n g hg hb

end ModifiedCartan
