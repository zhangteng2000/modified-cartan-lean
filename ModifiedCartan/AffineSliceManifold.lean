import ModifiedCartan.ManifoldDiscs
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option autoImplicit false
open Set Topology Manifold
open scoped Manifold ContDiff
namespace ModifiedCartan

theorem translation_mem_maximalAtlas {p : ℕ} (a : Fin p → ℂ) :
    (Homeomorph.addRight a).toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℂ, Fin p → ℂ) 1 (Fin p → ℂ) := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1
      (fun x => x + a) Set.univ
    exact (contMDiff_id.add contMDiff_const).contMDiffOn
  · change ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1
      (fun x => x - a) Set.univ
    rw [contMDiffOn_iff_contDiffOn]
    exact (contDiff_id.sub contDiff_const).contDiffOn

theorem affine_open_slice_isImmersion {p : ℕ} (S : Submodule ℂ (Fin p → ℂ))
    (a : Fin p → ℂ) (U : TopologicalSpace.Opens S) :
    IsImmersion 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) 1
      (fun x : U => a + (x.val : Fin p → ℂ)) := by
  obtain ⟨T, hT⟩ := S.exists_isCompl
  let e : (S × T) ≃L[ℂ] (Fin p → ℂ) := (S.prodEquivOfIsCompl T hT).toContinuousLinearEquiv
  apply IsImmersionOfComplement.isImmersion (F := T)
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (by fun_prop) e (chartAt S x) (Homeomorph.addRight (-a)).toOpenPartialHomeomorph
    (mem_chart_source S x) (by simp)
    (IsManifold.chart_mem_maximalAtlas x) (translation_mem_maximalAtlas (-a))
  intro v hv
  have hinv : ((chartAt S x).symm v).val = v := by
    have h := (chartAt S x).right_inv (by simpa using hv)
    simpa [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq] using h
  change a + (((chartAt S x).symm v).val : Fin p → ℂ) + -a = e (v, 0)
  rw [hinv]
  change a + (v : Fin p → ℂ) + -a = (v : Fin p → ℂ) + 0
  abel

theorem affine_open_slice_isEmbedding {p : ℕ} (S : Submodule ℂ (Fin p → ℂ))
    (a : Fin p → ℂ) (U : TopologicalSpace.Opens S) :
    IsEmbedding (fun x : U => a + (x.val : Fin p → ℂ)) := by
  exact (Homeomorph.addLeft a).isEmbedding.comp
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)

/-- A global open affine coordinate chart gives an actual complex immersion. -/
theorem affine_chart_isImmersion {p : ℕ} (S : Submodule ℂ (Fin p → ℂ))
    (a : Fin p → ℂ) {M : Type*} [TopologicalSpace M] [Nonempty M]
    {f : M → S} (hf : IsOpenEmbedding f) :
    letI := hf.singletonChartedSpace
    IsImmersion 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) 1 (fun x => a + (f x : Fin p → ℂ)) := by
  letI := hf.singletonChartedSpace
  letI : IsManifold 𝓘(ℂ, S) 1 M := hf.isManifold_singleton
  obtain ⟨T, hT⟩ := S.exists_isCompl
  let e : (S × T) ≃L[ℂ] (Fin p → ℂ) := (S.prodEquivOfIsCompl T hT).toContinuousLinearEquiv
  apply IsImmersionOfComplement.isImmersion (F := T)
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (continuous_const.add (continuous_subtype_val.comp hf.continuous)).continuousAt
    e (chartAt S x) (Homeomorph.addRight (-a)).toOpenPartialHomeomorph
    (mem_chart_source S x) (by simp)
    (IsManifold.chart_mem_maximalAtlas x) (translation_mem_maximalAtlas (-a))
  intro v hv
  have hinv : f ((chartAt S x).symm v) = v := by
    have h := (chartAt S x).right_inv (by simpa using hv)
    rwa [hf.singletonChartedSpace_chartAt_eq] at h
  change a + (f ((chartAt S x).symm v) : Fin p → ℂ) + -a = e (v, 0)
  rw [hinv]
  change a + (v : Fin p → ℂ) + -a = (v : Fin p → ℂ) + 0
  abel

end ModifiedCartan
