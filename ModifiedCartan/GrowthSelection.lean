import ModifiedCartan.Growth
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
set_option autoImplicit false
open Filter Topology Set
namespace ModifiedCartan

/-- Select the actual growth radii uniformly along a diverging sequence. -/
theorem select_growth_radii (M : ℕ → ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ n, ContinuousOn (M n) (Icc a b)) (hm : ∀ n, MonotoneOn (M n) (Icc a b))
    (hlim : Tendsto (fun n => M n a) atTop atTop) :
    ∃ ρ : ℕ → ℝ, (∀ n, a ≤ ρ n ∧ ρ n < b) ∧
      Tendsto (fun n => M n (ρ n)) atTop atTop ∧
      ∀ᶠ n in atTop, 0 < M n (ρ n) ∧ ρ n + 1 / M n (ρ n) < b ∧
        M n (ρ n + 1 / M n (ρ n)) ≤ 2 * M n (ρ n) := by
  classical
  let P := fun n => 0 < M n a ∧ 2 / M n a < b - a
  have hgood : ∀ᶠ n in atTop, P n := by
    filter_upwards [hlim.eventually (eventually_gt_atTop (max 0 (2 / (b - a))))] with n hn
    have hMa : 0 < M n a := (le_max_left _ _).trans_lt hn
    refine ⟨hMa, (div_lt_iff₀ hMa).mpr ?_⟩
    have h2 := (div_lt_iff₀ (sub_pos.mpr hab)).mp ((le_max_right _ _).trans_lt hn)
    nlinarith only [h2]
  have hex : ∀ n, ∃ r : ℝ, (a ≤ r ∧ r < b) ∧ (P n →
      0 < M n r ∧ r + 1 / M n r < b ∧ M n (r + 1 / M n r) ≤ 2 * M n r) := by
    intro n
    by_cases hn : P n
    · have hpos : ∀ x ∈ Icc a b, 0 < M n x :=
        fun x hx => hn.1.trans_le (hm n ⟨le_rfl, hab.le⟩ hx hx.1)
      obtain ⟨r, har, hrb, hgap, hdouble⟩ := growthLemma_proved (M n) a b hab (hc n) (hm n) hpos hn.2
      exact ⟨r, ⟨har, hrb⟩, fun _ => ⟨hpos r ⟨har, hrb.le⟩, hgap, hdouble⟩⟩
    · exact ⟨a, ⟨le_rfl, hab⟩, fun h => False.elim (hn h)⟩
  choose ρ hρ hrule using hex
  refine ⟨ρ, hρ, ?_, ?_⟩
  · apply tendsto_atTop_mono _ hlim
    intro n
    exact hm n ⟨le_rfl, hab.le⟩ ⟨(hρ n).1, (hρ n).2.le⟩ (hρ n).1
  · exact hgood.mono (fun n hn => hrule n hn)

end ModifiedCartan
