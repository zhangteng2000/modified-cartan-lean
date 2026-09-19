import ModifiedCartan.ProjectiveBlocks
import ModifiedCartan.ProjectiveHolomorphy

noncomputable section
set_option autoImplicit false
open Set Filter Topology Finset
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

theorem projectivePoint_smul {p : ℕ} (base : Fin p) {x : Fin p → ℂ}
    (hx : x ≠ 0) {c : ℂ} (hc : c ≠ 0) : projectivePoint base (c • x) = projectivePoint base x := by
  have hn : c • x ≠ 0 := smul_ne_zero hc hx
  apply projectiveKernel_injective p
  change projectiveKernelCoordinates (projectivePoint base (c • x)).rep =
    projectiveKernelCoordinates (projectivePoint base x).rep
  rw [projectivePoint_eq_mk base hn, projectivePoint_eq_mk base hx,
    projectiveKernelCoordinates_mk, projectiveKernelCoordinates_mk]
  exact projectiveKernelCoordinates_smul x hc

/-- The actual coordinate projection X_p -> projective space on the indices I. -/
def projectiveProjection {p : ℕ} (I : Finset (Fin p)) (hI : I.Nonempty)
    (q : ProjectiveX p) : ℙ ℂ (Fin I.card → ℂ) :=
  projectivePoint (blockBase hI) (fun j => q.val.rep (blockIndex I j))

def projectiveCurveFamily {p : ℕ} (base : Fin p) (F : ℕ → ℂ → ProjectiveX p) : Family p :=
  fun j n z => normalizeCoordinates base (F n z).val.rep j

theorem projectiveCurveFamily_units {p : ℕ} (base : Fin p)
    {F : ℕ → ℂ → ProjectiveX p}
    (hF : ∀ n, ProjectiveHolomorphicOn (fun z => (F n z).val) (disk 1)) :
    UnitFamily (projectiveCurveFamily base F) := by
  intro j n
  exact projective_unit_coordinate (hF n) (fun z _ j => (F n z).property.1 j) base j

theorem projectiveCurveFamily_zeroSum {p : ℕ} (base : Fin p)
    (F : ℕ → ℂ → ProjectiveX p) : ZeroSum (projectiveCurveFamily base F) := by
  intro n z hz
  simp only [projectiveCurveFamily, normalizeCoordinates, ← sum_div, (F n z).property.2, zero_div]

theorem projectiveProjection_curveFamily {p : ℕ} (base : Fin p)
    (F : ℕ → ℂ → ProjectiveX p) (I : Finset (Fin p)) (hI : I.Nonempty) (n : ℕ) (z : ℂ) :
    blockProjective (projectiveCurveFamily base F) I hI n z = projectiveProjection I hI (F n z) := by
  let x : Fin I.card → ℂ := fun j => (F n z).val.rep (blockIndex I j)
  have hx : x ≠ 0 := fun h => (F n z).property.1 (blockIndex I (blockBase hI)) (congrFun h (blockBase hI))
  have he : (fun j => normalizeCoordinates base (F n z).val.rep (blockIndex I j)) =
      ((F n z).val.rep base)⁻¹ • x := by
    funext j
    simp only [normalizeCoordinates, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, x]
    ring
  change projectivePoint (blockBase hI) (fun j => normalizeCoordinates base (F n z).val.rep (blockIndex I j)) =
    projectivePoint (blockBase hI) x
  rw [he]
  exact projectivePoint_smul (blockBase hI) hx (inv_ne_zero ((F n z).property.1 base))

/-- A unit zero-sum tuple defines an actual X_p-valued curve. Values outside
the manuscript's open disk are supplied only to make a total Lean function. -/
def familyProjectiveCurve {p : ℕ} (base : Fin p) (q0 : ProjectiveX p)
    (f : Family p) (hf : UnitFamily f) (hs : ZeroSum f) (n : ℕ) (z : ℂ) : ProjectiveX p := by
  classical
  exact if hz : z ∈ disk 1 then
    ⟨familyProjective base f n z, by
      have hn : (fun j => f j n z) ≠ 0 := fun h => (hf base n).2 z hz (congrFun h base)
      change homogeneousZeroSum (projectivePoint base (fun j => f j n z)).rep
      rw [projectivePoint_eq_mk base hn]
      exact (homogeneousZeroSum_projective_mk hn).mpr ⟨fun j => (hf j n).2 z hz, hs n z hz⟩⟩
  else q0

theorem familyProjectiveCurve_val {p : ℕ} (base : Fin p) (q0 : ProjectiveX p)
    (f : Family p) (hf : UnitFamily f) (hs : ZeroSum f) (n : ℕ) {z : ℂ} (hz : z ∈ disk 1) :
    (familyProjectiveCurve base q0 f hf hs n z).val = familyProjective base f n z := by
  simp [familyProjectiveCurve, hz]

theorem familyProjectiveCurve_holomorphic {p : ℕ} (base : Fin p) (q0 : ProjectiveX p)
    (f : Family p) (hf : UnitFamily f) (hs : ZeroSum f) (n : ℕ) :
    ProjectiveHolomorphicOn (fun z => (familyProjectiveCurve base q0 f hf hs n z).val) (disk 1) := by
  have heq : EqOn (fun z => (familyProjectiveCurve base q0 f hf hs n z).val)
      (familyProjective base f n) (disk 1) := fun z hz => familyProjectiveCurve_val base q0 f hf hs n hz
  have hh := familyProjective_holomorphic base hf n
  refine ⟨hh.1.congr heq, ?_⟩
  intro k j
  have hsubset : disk 1 ∩ (fun z => (familyProjectiveCurve base q0 f hf hs n z).val) ⁻¹' projectiveChartSet k ⊆
      disk 1 ∩ (familyProjective base f n) ⁻¹' projectiveChartSet k := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change (familyProjective base f n z).rep k ≠ 0
    rw [← heq hz.1]
    exact hz.2
  apply ((hh.2 k j).mono hsubset).congr
  intro z hz
  rw [heq hz.1]

theorem projectiveProjection_familyCurve {p : ℕ} (base : Fin p) (q0 : ProjectiveX p)
    (f : Family p) (hf : UnitFamily f) (hs : ZeroSum f)
    (I : Finset (Fin p)) (hI : I.Nonempty) (n : ℕ) {z : ℂ} (hz : z ∈ disk 1) :
    projectiveProjection I hI (familyProjectiveCurve base q0 f hf hs n z) = blockProjective f I hI n z := by
  have hn : (fun j => f j n z) ≠ 0 := fun h => (hf base n).2 z hz (congrFun h base)
  have hval := familyProjectiveCurve_val base q0 f hf hs n hz
  rw [familyProjective, projectivePoint_eq_mk base hn] at hval
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) (fun j => f j n z) hn
  have hrep : (familyProjectiveCurve base q0 f hf hs n z).val.rep = c • (fun j => f j n z) :=
    (congrArg Projectivization.rep hval).trans hc.symm
  unfold projectiveProjection
  rw [hrep]
  change projectivePoint (blockBase hI) ((c : ℂ) • (fun j => f (blockIndex I j) n z)) =
    projectivePoint (blockBase hI) (fun j => f (blockIndex I j) n z)
  exact projectivePoint_smul (blockBase hI)
    (fun h => (hf (blockIndex I (blockBase hI)) n).2 z hz (congrFun h (blockBase hI))) c.ne_zero

end ModifiedCartan
