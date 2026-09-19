import ModifiedCartan.ProjectiveConvergence
import ModifiedCartan.UniformComposition

noncomputable section
set_option autoImplicit false
open Set Topology Filter
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

/-- Total extension of projectivization; the fallback only supplies a value at
the zero vector. Every analytic use below proves its vector is nonzero. -/
def projectivePoint {p : ℕ} (k : Fin p) (x : Fin p → ℂ) : ℙ ℂ (Fin p → ℂ) :=
  if hx : x ≠ 0 then Projectivization.mk ℂ x hx else
    Projectivization.mk ℂ (fun _ : Fin p => (1 : ℂ))
      (fun h => one_ne_zero (congrFun h k))

theorem projectivePoint_eq_mk {p : ℕ} (k : Fin p) {x : Fin p → ℂ} (hx : x ≠ 0) :
    projectivePoint k x = Projectivization.mk ℂ x hx := by simp [projectivePoint, hx]

theorem projectivePoint_continuousAt {p : ℕ} (k : Fin p) {x : Fin p → ℂ} (hx : x ≠ 0) :
    ContinuousAt (projectivePoint k) x := by
  have hc : ContinuousOn (projectivePoint k) {x : Fin p → ℂ | x ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : ({x : Fin p → ℂ | x ≠ 0}.domRestrict (projectivePoint k)) =
        (Projectivization.mk' ℂ : {x : Fin p → ℂ // x ≠ 0} → ℙ ℂ (Fin p → ℂ)) := by
      funext x
      exact projectivePoint_eq_mk k x.property
    rw [he]
    exact (projective_mk_isQuotientMap p).continuous
  exact hc.continuousAt ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx)

theorem projectivePoint_normalize {p : ℕ} (base k : Fin p) {x : Fin p → ℂ} (hx : x ≠ 0) :
    normalizeCoordinates k (projectivePoint base x).rep = normalizeCoordinates k x := by
  rw [projectivePoint_eq_mk base hx, normalizeCoordinates_projective_mk]

theorem projectivePoint_coordinate_ne_zero {p : ℕ} (base k : Fin p)
    {x : Fin p → ℂ} (hx : x ≠ 0) : (projectivePoint base x).rep k ≠ 0 ↔ x k ≠ 0 := by
  rw [projectivePoint_eq_mk base hx]
  exact projective_mk_coordinate_ne_zero k hx

theorem projectivePoint_holomorphic {p : ℕ} (base : Fin p)
    {g : ℂ → Fin p → ℂ} {U : Set ℂ}
    (hg : ∀ j, DifferentiableOn ℂ (fun z => g z j) U) (hn : ∀ z ∈ U, g z ≠ 0) :
    ProjectiveHolomorphicOn (fun z => projectivePoint base (g z)) U := by
  have hc : ContinuousOn g U := continuousOn_pi.mpr (fun j => (hg j).continuousOn)
  refine ⟨fun z hz => (projectivePoint_continuousAt base (hn z hz)).comp_continuousWithinAt (hc z hz), ?_⟩
  intro k j
  have hd : DifferentiableOn ℂ (fun z => g z j / g z k)
      (U ∩ (fun z => projectivePoint base (g z)) ⁻¹' projectiveChartSet k) :=
    ((hg j).mono inter_subset_left).div ((hg k).mono inter_subset_left)
      (fun z hz => (projectivePoint_coordinate_ne_zero base k (hn z hz.1)).mp hz.2)
  apply hd.congr
  intro z hz
  exact congrFun (projectivePoint_normalize base k (hn z hz.1)) j

theorem projectivePoint_convergence {p : ℕ} (base : Fin p)
    {f : ℕ → ℂ → Fin p → ℂ} {g : ℂ → Fin p → ℂ} {U : Set ℂ}
    (hg : ∀ j, ContinuousOn (fun z => g z j) U)
    (hlim : ∀ j, TendstoLocallyUniformlyOn (fun n z => f n z j) (fun z => g z j) atTop U)
    (hn : ∀ z ∈ U, g z ≠ 0) :
    TendstoLocallyUniformlyOn (fun n z => projectivePoint base (f n z))
      (fun z => projectivePoint base (g z)) atTop U :=
  locallyUniform_comp_continuousAt (locallyUniform_pi hg hlim) (continuousOn_pi.mpr hg)
    (fun z hz => projectivePoint_continuousAt base (hn z hz))

end ModifiedCartan
