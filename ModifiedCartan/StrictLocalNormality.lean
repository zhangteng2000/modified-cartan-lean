import ModifiedCartan.LocalNormality
import Mathlib.Order.Filter.Finite

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

/-- Strict subsequences suffice in the local normality criterion when the
individual functions are continuous near the point. -/
theorem equicontinuousAt_of_strict_local_subsequence_limits {X Y : Type*}
    [MetricSpace X] [PseudoMetricSpace Y] (F : ℕ → X → Y) (x : X)
    {U : Set X} (hU : U ∈ 𝓝 x) (hF : ∀ n, ContinuousOn (F n) U)
    (h : ∀ σ : ℕ → ℕ, StrictMono σ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ V : Set X, V ∈ 𝓝 x ∧ ∃ G : X → Y, ContinuousOn G V ∧
        TendstoLocallyUniformlyOn (fun n => F (σ (φ n))) G atTop V) :
    EquicontinuousAt F x := by
  classical
  apply equicontinuousAt_of_local_subsequence_limits
  intro σ
  by_cases hrep : ∃ i : ℕ, ∃ᶠ n in atTop, σ n = i
  · obtain ⟨i, hi⟩ := hrep
    obtain ⟨φ, hφ, hσ⟩ := extraction_of_frequently_atTop hi
    refine ⟨φ, hφ, U, hU, F i, hF i, ?_⟩
    have he : (fun n => F (σ (φ n))) = (fun _ : ℕ => F i) := by
      funext n
      rw [hσ n]
    rw [he]
    have hc : TendstoUniformlyOn (fun _ : ℕ => F i) (F i) atTop U := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      exact Eventually.of_forall (fun n y hy => by simpa using hε)
    exact hc.tendstoLocallyUniformlyOn
  · have hσ : Tendsto σ atTop atTop := by
      apply tendsto_atTop.mpr
      intro N
      have he : ∀ i ∈ Finset.range N, ∀ᶠ n in atTop, σ n ≠ i := by
        intro i _
        exact not_frequently.mp (fun hi => hrep ⟨i, hi⟩)
      filter_upwards [(eventually_all_finset (Finset.range N)).mpr he] with n hn
      by_contra hlt
      exact hn (σ n) (Finset.mem_range.mpr (by omega)) rfl
    obtain ⟨τ, hτ, hστ⟩ := strictMono_subseq_of_tendsto_atTop hσ
    obtain ⟨φ, hφ, V, hV, G, hG, hlim⟩ := h (σ ∘ τ) hστ
    exact ⟨τ ∘ φ, hτ.comp hφ, V, hV, G, hG, hlim⟩

end ModifiedCartan
