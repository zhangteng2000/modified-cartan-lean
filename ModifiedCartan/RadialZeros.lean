import ModifiedCartan.ZeroFactors
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

def radialZeroSet (F : ℂ → ℂ) (b c : ℝ) : Set ℝ :=
  {r | r ∈ Icc b c ∧ ∃ z : ℂ, ‖z‖ = r ∧ F z = 0}

/-- Only finitely many radii in a compact inner band meet a zero of a
nontrivial holomorphic function. This includes endpoint radii. -/
theorem radialZeroSet_finite {F : ℂ → ℂ} {b c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hF : DifferentiableOn ℂ F (disk 1)) (hn : ∃ w ∈ disk 1, F w ≠ 0) :
    (radialZeroSet F b c).Finite := by
  classical
  obtain ⟨w,hw,hnw⟩ := hn
  obtain ⟨s,m,Q,_hs,_hQ,hQnz,hfact⟩ := finite_zero_factorization hF hw hnw hc hc1
  apply (s.image norm).finite_toSet.subset
  rintro r ⟨hr,z,hz,hzero⟩
  by_contra hnot
  have hzc : z ∈ closedBall (0 : ℂ) c := by simpa using hz.trans_le hr.2
  have hFnz : F z ≠ 0 := by
    rw [hfact z (closedBall_subset_ball hc1 hzc)]
    apply mul_ne_zero _ (hQnz z hzc)
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro he
    apply hnot
    exact Finset.mem_image.mpr ⟨t,ht,by simpa [he] using hz⟩
  exact hFnz hzero

theorem radialZeroSet_volume_zero {F : ℂ → ℂ} {b c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hF : DifferentiableOn ℂ F (disk 1)) (hn : ∃ w ∈ disk 1, F w ≠ 0) :
    volume (radialZeroSet F b c) = 0 := (radialZeroSet_finite hc hc1 hF hn).measure_zero volume

/-- Removing zero circles for finitely many actual holomorphic functions
preserves the outer measure of an arbitrary radius set. -/
theorem exists_zero_free_circle_subset {ι : Type*} [Fintype ι] (F : ι → ℂ → ℂ)
    {b c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hF : ∀ i, DifferentiableOn ℂ (F i) (disk 1))
    (hn : ∀ i, ∃ w ∈ disk 1, F i w ≠ 0) (S : Set ℝ) (hS : S ⊆ Icc b c) :
    ∃ S' : Set ℝ, S' ⊆ S ∧ volume S' = volume S ∧
      ∀ r ∈ S', ∀ i, ∀ z ∈ sphere (0 : ℂ) r, F i z ≠ 0 := by
  let E := ⋃ i, radialZeroSet (F i) b c
  have hE : volume E = 0 := by
    apply le_antisymm _ (by positivity)
    exact (measure_iUnion_fintype_le volume (fun i => radialZeroSet (F i) b c)).trans
      (by simp [radialZeroSet_volume_zero hc hc1 (hF _) (hn _)])
  refine ⟨S \ E,sdiff_subset,measure_sdiff_null hE,?_⟩
  intro r hr i z hz hzero
  apply hr.2
  exact mem_iUnion.mpr ⟨i,hS hr.1,z,by simpa using hz,hzero⟩

end ModifiedCartan
