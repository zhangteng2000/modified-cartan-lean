import ModifiedCartan.CartanThreeLocal
import ModifiedCartan.CompactNormality
import ModifiedCartan.ProjectiveKernelInverse
import ModifiedCartan.FiveClassReduction

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

/-- Global normality of the genuine projective maps for three-term unit sums. -/
theorem three_global_projective_limit {f : Family 3} (hf : UnitFamily f) (hs : ZeroSum f) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℙ ℂ (Fin 3 → ℂ),
      ContinuousOn G (disk 1) ∧ MapsTo G (disk 1) (projectiveHyperplane 3) ∧
      TendstoLocallyUniformlyOn (fun n => familyProjective 0 f (φ n)) G atTop (disk 1) := by
  obtain ⟨φ, hφ, H, hH, hmap, hlim⟩ := equicontinuous_compact_range_subsequence isOpen_ball
    (fun n z => projectiveKernel (familyProjective 0 f n z))
    (fun n => (projectiveKernel_continuous 3).comp_continuousOn (familyProjective_holomorphic 0 hf n).1)
    (three_projectiveKernel_equicontinuous hf hs) (isCompact_range (projectiveKernel_continuous 3))
    (fun n z _ => mem_range_self _)
  obtain ⟨G, hG, _, hconv⟩ := projectiveKernel_lift_convergence 0 hH hmap hlim
  refine ⟨φ, hφ, G, hG, ?_, hconv⟩
  intro z hz
  apply (projectiveHyperplane_isClosed 3).mem_of_tendsto (hconv.tendsto_at hz)
  apply Eventually.of_forall
  intro n
  exact projectivePoint_mem_hyperplane 0
    (fun he => (hf 0 (φ n)).2 z hz (congrFun he 0)) (hs (φ n) z hz)

/-- The full-disk base of classical Cartan extraction is proved, without an
assumed normal-family theorem or a shrunken disk. -/
theorem cartanExtraction_three : CartanExtractionAt 3 := by
  intro f hf hs
  obtain ⟨φ, hφ, G, _, hG, hlim⟩ := three_global_projective_limit hf hs
  refine ⟨φ, hφ, Or.inl ?_⟩
  exact cclass_univ_of_projective_limit 0 ⟨0, by simp [disk]⟩ isOpen_ball
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
    (fun j n => hf j (φ n)) hG hlim

theorem partitionProperty_three : PartitionProperty 3 (disk 1) := by
  intro f hf hs
  obtain ⟨φ, hφ, G, _, hG, hlim⟩ := three_global_projective_limit hf hs
  refine ⟨φ, hφ, cpartition_single_class ?_⟩
  exact cclass_univ_of_projective_limit 0 ⟨0, by simp [disk]⟩ isOpen_ball
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
    (fun j n => hf j (φ n)) hG hlim

end ModifiedCartan
