import ModifiedCartan.ProjectiveCompact
import ModifiedCartan.Hurwitz
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
set_option autoImplicit false
open Set Topology Filter Metric
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

theorem projectiveKernel_component_continuous {p : ℕ} (j k : Fin p) :
    Continuous (fun q : ℙ ℂ (Fin p → ℂ) => projectiveKernel q j k) :=
  (continuous_apply k).comp ((continuous_apply j).comp (projectiveKernel_continuous p))

theorem projectiveCoordinate_continuousOn {p : ℕ} (k j : Fin p) :
    ContinuousOn (fun q : ℙ ℂ (Fin p → ℂ) => normalizeCoordinates k q.rep j)
      (projectiveChartSet k) := by
  have h := (projectiveKernel_component_continuous j k).continuousOn.div
    (projectiveKernel_component_continuous k k).continuousOn
    (fun q hq => projectiveKernelCoordinates_diagonal_ne_zero q.rep_nonzero hq)
  apply h.congr
  intro q hq
  exact (projectiveKernelCoordinates_ratio q.rep_nonzero hq j).symm

/-- Convergence is in the uniformity of the actual projective quotient. On a
chart avoided by the sequence and its limit it implies convergence of the
genuine affine coordinate ratios. -/
theorem projective_convergence_coordinates {p : ℕ}
    {F : ℕ → ℂ → ℙ ℂ (Fin p → ℂ)} {G : ℂ → ℙ ℂ (Fin p → ℂ)} {U : Set ℂ}
    (hG : ContinuousOn G U) (hconv : TendstoLocallyUniformlyOn F G atTop U)
    (k j : Fin p) (hkF : ∀ n z, z ∈ U → (F n z).rep k ≠ 0)
    (hkG : ∀ z ∈ U, (G z).rep k ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n z => normalizeCoordinates k (F n z).rep j)
      (fun z => normalizeCoordinates k (G z).rep j) atTop U := by
  have hc (a b : Fin p) := (projectiveKernel_component_continuous a b).comp_continuousOn hG
  have hl (a b : Fin p) :=
    (CompactSpace.uniformContinuous_of_continuous (projectiveKernel_component_continuous a b)).comp_tendstoLocallyUniformlyOn hconv
  have hd := (hl j k).div₀ (hl k k) (hc j k) (hc k k)
    (fun z hz => projectiveKernelCoordinates_diagonal_ne_zero (G z).rep_nonzero (hkG z hz))
  apply (hd.congr (fun n z hz => projectiveKernelCoordinates_ratio (F n z).rep_nonzero (hkF n z hz) j)).congr_right
  intro z hz
  exact projectiveKernelCoordinates_ratio (G z).rep_nonzero (hkG z hz) j

/-- Holomorphy in the standard projective affine charts, whose actual
homeomorphisms are constructed in ProjectiveTopology. -/
def ProjectiveHolomorphicOn {p : ℕ} (F : ℂ → ℙ ℂ (Fin p → ℂ)) (U : Set ℂ) : Prop :=
  ContinuousOn F U ∧ ∀ k j : Fin p,
    DifferentiableOn ℂ (fun z => normalizeCoordinates k (F z).rep j)
      (U ∩ F ⁻¹' projectiveChartSet k)

theorem projectiveHolomorphicOn_mono {p : ℕ} {F : ℂ → ℙ ℂ (Fin p → ℂ)}
    {U V : Set ℂ} (hF : ProjectiveHolomorphicOn F U) (hVU : V ⊆ U) :
    ProjectiveHolomorphicOn F V :=
  ⟨hF.1.mono hVU, fun k j => (hF.2 k j).mono (fun _ hz => ⟨hVU hz.1, hz.2⟩)⟩

theorem projective_unit_coordinate {p : ℕ} {F : ℂ → ℙ ℂ (Fin p → ℂ)}
    {U : Set ℂ} (hF : ProjectiveHolomorphicOn F U)
    (hunit : ∀ z ∈ U, ∀ j, (F z).rep j ≠ 0) (k j : Fin p) :
    IsHolomorphicUnit (fun z => normalizeCoordinates k (F z).rep j) U := by
  refine ⟨(hF.2 k j).mono (fun z hz => ⟨hz, hunit z hz k⟩), ?_⟩
  intro z hz
  exact div_ne_zero (hunit z hz j) (hunit z hz k)

end ModifiedCartan
