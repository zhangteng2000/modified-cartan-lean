import ModifiedCartan.CompactNormality
import ModifiedCartan.ProjectiveKernelInverse

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

theorem projective_limit_of_kernel_equicontinuous {p : ℕ} (base : Fin p)
    {f : Family p} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    (hs : ∀ n z, z ∈ U → ∑ j, f j n z = 0)
    (heq : Equicontinuous (fun n (z : U) => projectiveKernel (familyProjective base f n z))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℙ ℂ (Fin p → ℂ),
      ContinuousOn G U ∧ MapsTo G U (projectiveHyperplane p) ∧
      TendstoLocallyUniformlyOn (fun n => familyProjective base f (φ n)) G atTop U := by
  obtain ⟨φ, hφ, H, hH, hmap, hlim⟩ := equicontinuous_compact_range_subsequence hU
    (fun n z => projectiveKernel (familyProjective base f n z))
    (fun n => (projectiveKernel_continuous p).comp_continuousOn (familyProjective_holomorphic base hf n).1)
    heq (isCompact_range (projectiveKernel_continuous p))
    (fun n z _ => mem_range_self _)
  obtain ⟨G, hG, _, hconv⟩ := projectiveKernel_lift_convergence base hH hmap hlim
  refine ⟨φ, hφ, G, hG, ?_, hconv⟩
  intro z hz
  apply (projectiveHyperplane_isClosed p).mem_of_tendsto (hconv.tendsto_at hz)
  apply Eventually.of_forall
  intro n
  exact projectivePoint_mem_hyperplane base
    (fun he => (hf base (φ n)).2 z hz (congrFun he base)) (hs (φ n) z hz)


end ModifiedCartan
