import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import ModifiedCartan.Basic

noncomputable section
set_option autoImplicit false
open Set Filter Topology Manifold
open scoped Manifold ContDiff
namespace ModifiedCartan

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) 1 M]

/-- A local immersion has a differentiable local left inverse. -/
theorem immersion_local_left_inverse {f : M → V} {x : M}
    (hf : IsImmersionAt 𝓘(ℂ, E) 𝓘(ℂ, V) 1 f x) :
    ∃ r : V → M, ContMDiffAt 𝓘(ℂ, V) 𝓘(ℂ, E) 1 r (f x) ∧
      (r ∘ f) =ᶠ[𝓝 x] id := by
  let h := hf.isImmersionAtOfComplement_complement
  let p : V → E := fun y => (h.equiv.symm y).1
  let r : V → M := h.domChart.symm ∘ p ∘ h.codChart
  have heq : ∀ y ∈ h.domChart.source, p (h.codChart (f y)) = h.domChart y := by
    intro y hy
    have hmem : h.domChart y ∈ (h.domChart.extend 𝓘(ℂ, E)).target := by
      simpa using h.domChart.map_source hy
    have hchart := h.writtenInCharts hmem
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      id_eq, h.domChart.left_inv hy] at hchart
    dsimp [p]
    rw [hchart]
    simp
  have hleft : (r ∘ f) =ᶠ[𝓝 x] id := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    dsimp [r]
    rw [heq y hy, h.domChart.left_inv hy]
  refine ⟨r, ?_, hleft⟩
  have hp : ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, E) 1 p := by
    rw [contMDiff_iff_contDiff]
    dsimp [p]
    fun_prop
  have hc := contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
    h.mem_codChart_source
  have hr := contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
    (h.domChart.map_source h.mem_domChart_source)
  have hx : p (h.codChart (f x)) = h.domChart x := heq x h.mem_domChart_source
  have hr' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) 1 h.domChart.symm
      (p (h.codChart (f x))) := hx.symm ▸ hr
  exact hr'.comp (f x) ((hp.contMDiffAt).comp (f x) hc)

/-- The differential of a complex immersion is injective. -/
theorem immersion_mfderiv_injective {f : M → V} {x : M}
    (hf : IsImmersionAt 𝓘(ℂ, E) 𝓘(ℂ, V) 1 f x) :
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, V) f x) := by
  obtain ⟨r, hr, heq⟩ := immersion_local_left_inverse hf
  have hcomp := mfderiv_comp x (hr.mdifferentiableAt (by norm_num))
    (hf.contMDiffAt.mdifferentiableAt (by norm_num))
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  intro a b hab
  have h := congrArg (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, E) r (f x)) hab
  have ha := congrArg (fun L => L a) hcomp
  have hb := congrArg (fun L => L b) hcomp
  exact ha.trans (h.trans hb.symm)

end ModifiedCartan
