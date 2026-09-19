import ModifiedCartan.UniformComposition
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- If every selected sequence has a continuous locally uniform limit near a
point after extraction, the original family is equicontinuous at that point. -/
theorem equicontinuousAt_of_local_subsequence_limits {X Y ι : Type*}
    [MetricSpace X] [PseudoMetricSpace Y] (F : ι → X → Y) (x : X)
    (h : ∀ σ : ℕ → ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V : Set X, V ∈ 𝓝 x ∧
      ∃ G : X → Y, ContinuousOn G V ∧
        TendstoLocallyUniformlyOn (fun n => F (σ (φ n))) G atTop V) :
    EquicontinuousAt F x := by
  classical
  by_contra hn
  rw [Metric.equicontinuousAt_iff] at hn
  push Not at hn
  obtain ⟨ε, hε, hbad⟩ := hn
  have hex : ∀ n : ℕ, ∃ y : X, dist y x < 1 / (n + 1 : ℝ) ∧
      ∃ i : ι, ε ≤ dist (F i y) (F i x) := by
    intro n
    obtain ⟨y, hy, i, hi⟩ := hbad (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨y, hy, i, by simpa only [dist_comm] using hi⟩
  choose y hy i hi using hex
  have hsmall : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hyx : Tendsto y atTop (𝓝 x) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [hsmall.eventually (gt_mem_nhds hδ)] with n hn
    exact (hy n).trans hn
  obtain ⟨φ, hφ, V, hV, G, hG, hconv⟩ := h i
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hyφ : Tendsto (fun n => y (φ n)) atTop (𝓝[V] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hyx.comp hφ.tendsto_atTop, (hyx.comp hφ.tendsto_atTop).eventually hV⟩
  have hleft := hconv.tendsto_comp (hG x hxV) hxV hyφ
  have hright := hconv.tendsto_at hxV
  have hd : Tendsto (fun n => dist (F (i (φ n)) (y (φ n))) (F (i (φ n)) x)) atTop (𝓝 0) := by
    simpa only [dist_self] using hleft.dist hright
  have hle : ε ≤ 0 := ge_of_tendsto hd (Eventually.of_forall fun n => hi (φ n))
  linarith

end ModifiedCartan
