import ModifiedCartan.AffineSliceManifold

noncomputable section
set_option autoImplicit false
open Set Filter Topology Manifold
open scoped Manifold ContDiff
namespace ModifiedCartan

theorem affine_chart_mfderiv {p : ℕ} (S : Submodule ℂ (Fin p → ℂ))
    (a : Fin p → ℂ) {M : Type*} [TopologicalSpace M] [Nonempty M]
    {f : M → S} (hf : IsOpenEmbedding f) :
    letI := hf.singletonChartedSpace
    ∀ (x : M) (v : TangentSpace 𝓘(ℂ, S) x),
      mfderiv 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) (fun y => a + (f y : Fin p → ℂ)) x v =
        ((show S from v) : Fin p → ℂ) := by
  letI := hf.singletonChartedSpace
  letI : IsManifold 𝓘(ℂ, S) 1 M := hf.isManifold_singleton
  intro x v
  let e : M → Fin p → ℂ := fun y => a + (f y : Fin p → ℂ)
  have hm := (affine_chart_isImmersion S a hf).contMDiff.mdifferentiable (by norm_num)
  have hchart : ⇑(chartAt S x) = f := hf.singletonChartedSpace_chartAt_eq
  have hc : extChartAt 𝓘(ℂ, S) x x = f x := by simp [extChartAt_coe, hchart]
  have hnhds : (chartAt S x).target ∈ 𝓝 (f x) := by
    rw [← hchart]
    exact (chartAt S x).open_target.mem_nhds ((chartAt S x).map_source (mem_chart_source S x))
  have heq : writtenInExtChartAt 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) x e =ᶠ[𝓝 (f x)]
      (fun y : S => a + (y : Fin p → ℂ)) := by
    filter_upwards [hnhds] with y hy
    have hi : f ((chartAt S x).symm y) = y := by
      rw [← hchart]
      exact (chartAt S x).right_inv hy
    simpa [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, chartAt_self_eq, e]
      using congrArg (fun w : S => a + (w : Fin p → ℂ)) hi
  have hd : fderiv ℂ (writtenInExtChartAt 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) x e) (f x) =
      S.subtypeL :=
    heq.fderiv_eq.trans ((S.subtypeL.hasFDerivAt.const_add a).fderiv)
  change mfderiv 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) e x v = _
  unfold mfderiv
  erw [if_pos (hm x)]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  erw [hc, hd]
  rfl

theorem affine_open_slice_mfderiv {p : ℕ} (S : Submodule ℂ (Fin p → ℂ))
    (a : Fin p → ℂ) (U : TopologicalSpace.Opens S) (x : U)
    (v : TangentSpace 𝓘(ℂ, S) x) :
    mfderiv 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) (fun y : U => a + (y.val : Fin p → ℂ)) x v =
      ((show S from v) : Fin p → ℂ) := by
  let e : U → Fin p → ℂ := fun y => a + (y.val : Fin p → ℂ)
  have hm := (affine_open_slice_isImmersion S a U).contMDiff.mdifferentiable (by norm_num)
  have hchart : ⇑(chartAt S x) = Subtype.val := by
    funext y
    simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  have hc : extChartAt 𝓘(ℂ, S) x x = x.val := by
    simp [extChartAt_coe, hchart, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  have hnhds : (chartAt S x).target ∈ 𝓝 x.val := by
    rw [← hchart]
    exact (chartAt S x).open_target.mem_nhds ((chartAt S x).map_source (mem_chart_source S x))
  have heq : writtenInExtChartAt 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) x e =ᶠ[𝓝 x.val]
      (fun y : S => a + (y : Fin p → ℂ)) := by
    filter_upwards [hnhds] with y hy
    have hi : ((chartAt S x).symm y).val = y := by
      rw [← hchart]
      exact (chartAt S x).right_inv hy
    simpa [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, chartAt_self_eq, e]
      using congrArg (fun w : S => a + (w : Fin p → ℂ)) hi
  have hd : fderiv ℂ (writtenInExtChartAt 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) x e) x.val =
      S.subtypeL :=
    heq.fderiv_eq.trans ((S.subtypeL.hasFDerivAt.const_add a).fderiv)
  change mfderiv 𝓘(ℂ, S) 𝓘(ℂ, Fin p → ℂ) e x v = _
  unfold mfderiv
  erw [if_pos (hm x)]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  erw [hc, hd]
  rfl

end ModifiedCartan
