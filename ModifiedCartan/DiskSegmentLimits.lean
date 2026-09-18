import ModifiedCartan.DiskSegmentCompact
import ModifiedCartan.ParameterUniformConvergence

noncomputable section
set_option autoImplicit false
open Filter Topology Complex Metric Set
namespace ModifiedCartan

def scaledDiskSegment (R : ℝ) (a ξ : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (R : ℂ) * diskSegmentMap (a / (R : ℂ)) ξ t z

theorem scaledDiskSegment_joint_continuousAt {R t : ℝ} {a ξ z : ℂ}
    (hR : R ≠ 0) (ha : ‖a / (R : ℂ)‖ < 1) (hξ : ‖ξ‖ = 1)
    (ht : |t| < 1) (hz : z ∈ disk 1) :
    ContinuousAt (fun v : (ℝ × ℂ × ℂ × ℝ) × ℂ =>
      scaledDiskSegment v.1.1 v.1.2.1 v.1.2.2.1 v.1.2.2.2 v.2) ((R, a, ξ, t), z) := by
  have hRcont : ContinuousAt (fun v : (ℝ × ℂ × ℂ × ℝ) × ℂ => (v.1.1 : ℂ)) ((R, a, ξ, t), z) :=
    (Complex.continuous_ofReal.comp (by fun_prop)).continuousAt
  have hacont : ContinuousAt (fun v : (ℝ × ℂ × ℂ × ℝ) × ℂ => v.1.2.1 / (v.1.1 : ℂ)) ((R, a, ξ, t), z) :=
    (by fun_prop : ContinuousAt (fun v : (ℝ × ℂ × ℂ × ℝ) × ℂ => v.1.2.1) ((R, a, ξ, t), z)).div
      hRcont (Complex.ofReal_ne_zero.mpr hR)
  have hinner : ContinuousAt (fun v : (ℝ × ℂ × ℂ × ℝ) × ℂ =>
      diskSegmentMap (v.1.2.1 / (v.1.1 : ℂ)) v.1.2.2.1 v.1.2.2.2 v.2) ((R, a, ξ, t), z) := by
    apply ContinuousAt.comp
      (f := fun v : (ℝ × ℂ × ℂ × ℝ) × ℂ => (v.1.2.1 / (v.1.1 : ℂ), v.1.2.2.1, v.1.2.2.2, v.2))
      (g := fun p : ℂ × ℂ × ℝ × ℂ => diskSegmentMap p.1 p.2.1 p.2.2.1 p.2.2.2)
      (diskSegmentMap_joint_continuousAt ha hξ ht hz)
    exact hacont.prodMk (by fun_prop)
  exact hRcont.mul hinner

theorem scaledDiskSegment_compactConvergence {R t : ℕ → ℝ} {a ξ : ℕ → ℂ}
    {R₀ t₀ : ℝ} {a₀ ξ₀ : ℂ}
    (hR : Tendsto R atTop (𝓝 R₀)) (ha : Tendsto a atTop (𝓝 a₀))
    (hξ : Tendsto ξ atTop (𝓝 ξ₀)) (ht : Tendsto t atTop (𝓝 t₀))
    (hR₀ : R₀ ≠ 0) (ha₀ : ‖a₀ / (R₀ : ℂ)‖ < 1) (hξ₀ : ‖ξ₀‖ = 1) (ht₀ : |t₀| < 1) :
    CompactConvergence (fun n => scaledDiskSegment (R n) (a n) (ξ n) (t n))
      (scaledDiskSegment R₀ a₀ ξ₀ t₀) (disk 1) := by
  apply compactConvergence_of_parameter (F := fun p : ℝ × ℂ × ℂ × ℝ => scaledDiskSegment p.1 p.2.1 p.2.2.1 p.2.2.2)
    (u := fun n => (R n, a n, ξ n, t n)) (p := (R₀, a₀, ξ₀, t₀))
    (by simpa only [nhds_prod_eq] using hR.prodMk (ha.prodMk (hξ.prodMk ht)))
  intro z hz
  exact scaledDiskSegment_joint_continuousAt hR₀ ha₀ hξ₀ ht₀ hz

end ModifiedCartan
