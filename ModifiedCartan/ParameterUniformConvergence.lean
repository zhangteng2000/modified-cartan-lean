import ModifiedCartan.Convergence

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem continuous_parameter_uniformOn {P : Type*} [TopologicalSpace P]
    {F : P → ℂ → ℂ} {p : P} {K : Set ℂ} (hK : IsCompact K)
    (hF : ∀ z ∈ K, ContinuousAt (fun v : P × ℂ => F v.1 v.2) (p, z)) :
    TendstoUniformlyOn F (F p) (𝓝 p) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  apply hK.eventually_forall_of_forall_eventually
  intro z hz
  have hc : ContinuousAt (fun v : P × ℂ => F p v.2) (p, z) := by
    exact ContinuousAt.comp (f := fun v : P × ℂ => (p, v.2))
      (g := fun v : P × ℂ => F v.1 v.2) (hF z hz)
      (continuousAt_const.prodMk continuousAt_snd)
  have hd := hc.dist (hF z hz)
  exact hd.eventually (gt_mem_nhds (by simpa only [dist_self] using hε))

theorem compactConvergence_of_parameter {P : Type*} [TopologicalSpace P]
    {F : P → ℂ → ℂ} {p : P} {u : ℕ → P} {U : Set ℂ}
    (hu : Tendsto u atTop (𝓝 p))
    (hF : ∀ z ∈ U, ContinuousAt (fun v : P × ℂ => F v.1 v.2) (p, z)) :
    CompactConvergence (fun n => F (u n)) (F p) U := by
  intro K hKU hK
  exact (continuous_parameter_uniformOn hK (fun z hz => hF z (hKU hz))).seq_tendstoUniformlyOn u hu

end ModifiedCartan
