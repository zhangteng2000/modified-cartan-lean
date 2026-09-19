import ModifiedCartan.Convergence

noncomputable section
set_option autoImplicit false
open Set Filter Topology Uniformity
namespace ModifiedCartan

theorem joint_tendsto_of_locallyUniform {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {F : ℕ → X → Y} {g : X → Y} {U : Set X}
    (h : TendstoLocallyUniformlyOn F g atTop U) (hg : ContinuousOn g U)
    {x : X} (hx : x ∈ U) :
    Tendsto (fun y : ℕ × X => F y.1 y.2) (atTop ×ˢ 𝓝[U] x) (𝓝 (g x)) := by
  have he := tendstoLocallyUniformlyOn_iff_forall_tendsto.mp h x hx
  exact (Filter.Tendsto.comp (hg x hx) tendsto_snd).congr_uniformity he

theorem locallyUniform_of_joint_tendsto {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {F : ℕ → X → Y} {g : X → Y} {U : Set X} (hg : ContinuousOn g U)
    (h : ∀ x ∈ U, Tendsto (fun y : ℕ × X => F y.1 y.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (g x))) : TendstoLocallyUniformlyOn F g atTop U := by
  apply tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro x hx
  exact ((Filter.Tendsto.comp (hg x hx) tendsto_snd).prodMk_nhds (h x hx)).mono_right (nhds_le_uniformity _)

/-- A continuous postcomposition preserves local uniform convergence when the
limit is continuous. Only continuity at the actual limit values is needed. -/
theorem locallyUniform_comp_continuousAt {X Y Z : Type*} [TopologicalSpace X]
    [UniformSpace Y] [UniformSpace Z] {F : ℕ → X → Y} {g : X → Y} {U : Set X}
    (h : TendstoLocallyUniformlyOn F g atTop U) (hg : ContinuousOn g U)
    {a : Y → Z} (ha : ∀ x ∈ U, ContinuousAt a (g x)) :
    TendstoLocallyUniformlyOn (fun n x => a (F n x)) (fun x => a (g x)) atTop U := by
  apply locallyUniform_of_joint_tendsto (fun x hx => (ha x hx).comp_continuousWithinAt (hg x hx))
  intro x hx
  exact (ha x hx).tendsto.comp (joint_tendsto_of_locallyUniform h hg hx)

theorem locallyUniform_pi {X ι : Type*} {Y : ι → Type*} [TopologicalSpace X]
    [∀ j, UniformSpace (Y j)] {F : ℕ → X → ∀ j, Y j} {g : X → ∀ j, Y j} {U : Set X}
    (hg : ∀ j, ContinuousOn (fun x => g x j) U)
    (h : ∀ j, TendstoLocallyUniformlyOn (fun n x => F n x j) (fun x => g x j) atTop U) :
    TendstoLocallyUniformlyOn F g atTop U := by
  apply locallyUniform_of_joint_tendsto (continuousOn_pi.mpr hg)
  intro x hx
  apply tendsto_pi_nhds.mpr
  intro j
  exact joint_tendsto_of_locallyUniform (h j) (hg j) hx

end ModifiedCartan
