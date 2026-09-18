import ModifiedCartan.FailurePoints
import ModifiedCartan.Hurwitz

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem nonnegative_sequence_zero_subsequence {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hno : ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, ε ≤ u n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => u (φ n)) atTop (𝓝 0) := by
  have hsmall : ∀ K : Set ℂ, K ⊆ univ → IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ ∀ _z ∈ K, ‖(u n : ℂ)‖ < ε := by
    intro K _ _ ε hε N
    have hf : ∃ᶠ n in atTop, u n < ε := by
      show ¬ ∀ᶠ n in atTop, ¬ u n < ε
      simpa only [not_lt] using (show ¬ ∀ᶠ n in atTop, ε ≤ u n from fun h => hno ⟨ε, hε, h⟩)
    obtain ⟨n, hn, hb⟩ := frequently_atTop.mp hf N
    refine ⟨n, hn, fun _ _ => ?_⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hu n)] using hb
  obtain ⟨φ, hφ, hconv⟩ := compactConvergence_zero_subsequence_of_frequently_small
    (g := fun n (_ : ℂ) => (u n : ℂ)) isOpen_univ hsmall
  have hp := Complex.continuous_re.tendsto (0 : ℂ) |>.comp
    (compactConvergence_pointwise hconv (mem_univ (0 : ℂ)))
  exact ⟨φ, hφ, by simpa [Function.comp_def] using hp⟩

theorem nontrivial_on_smaller_disk {s : ℂ → ℂ} {r : ℝ}
    (hs : DifferentiableOn ℂ s (disk 1)) (hr : 0 < r) (_hr1 : r ≤ 1)
    (hne : ∃ z ∈ disk 1, s z ≠ 0) : ∃ z ∈ disk r, s z ≠ 0 := by
  by_contra h
  push Not at h
  have he : s =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
    exact h z hz
  have hall := (hs.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected (show (0 : ℂ) ∈ disk 1 by simp [disk])
    he
  obtain ⟨z, hz, hsz⟩ := hne
  exact hsz (hall hz)

end ModifiedCartan
