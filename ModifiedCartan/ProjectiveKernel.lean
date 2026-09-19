import ModifiedCartan.ProjectiveTopology
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
set_option autoImplicit false
open Set Topology
open scoped ComplexConjugate LinearAlgebra.Projectivization
namespace ModifiedCartan

/-- Scalar-invariant matrix coordinates on projective space. The ambient norm
is the actual finite-dimensional pi norm; no choice of representative remains. -/
def projectiveKernelCoordinates {p : ℕ} (x : Fin p → ℂ) : Fin p → Fin p → ℂ :=
  fun j k => x j * conj (x k) / (‖x‖ ^ 2 : ℝ)

theorem projectiveKernelCoordinates_smul {p : ℕ} (x : Fin p → ℂ) {c : ℂ} (hc : c ≠ 0) :
    projectiveKernelCoordinates (c • x) = projectiveKernelCoordinates x := by
  have hc2 : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
  funext j k
  simp only [projectiveKernelCoordinates, Pi.smul_apply, smul_eq_mul, map_mul, norm_smul,
    mul_pow, Complex.ofReal_mul]
  have hnum : c * x j * (conj c * conj (x k)) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) * (x j * conj (x k)) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  rw [hnum, mul_div_mul_left _ _ hc2]

theorem projectiveKernelCoordinates_mk {p : ℕ} {x : Fin p → ℂ} (hx : x ≠ 0) :
    projectiveKernelCoordinates (Projectivization.mk ℂ x hx).rep = projectiveKernelCoordinates x := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) x hx
  rw [← hc]
  exact projectiveKernelCoordinates_smul x c.ne_zero

def projectiveKernel {p : ℕ} (q : ℙ ℂ (Fin p → ℂ)) : Fin p → Fin p → ℂ :=
  projectiveKernelCoordinates q.rep

theorem projectiveKernel_continuous (p : ℕ) :
    Continuous (projectiveKernel : ℙ ℂ (Fin p → ℂ) → Fin p → Fin p → ℂ) := by
  apply (projective_mk_isQuotientMap p).continuous_iff.mpr
  have he : (projectiveKernel ∘ Projectivization.mk' ℂ) =
      (fun x : {x : Fin p → ℂ // x ≠ 0} => projectiveKernelCoordinates x.val) := by
    funext x
    exact projectiveKernelCoordinates_mk x.property
  rw [he]
  apply continuous_pi
  intro j
  apply continuous_pi
  intro k
  apply Continuous.div
  · exact ((continuous_apply j).comp continuous_subtype_val).mul
      (Complex.continuous_conj.comp ((continuous_apply k).comp continuous_subtype_val))
  · exact Complex.continuous_ofReal.comp (continuous_subtype_val.norm.pow 2)
  · intro x
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr x.property))

theorem projectiveKernelCoordinates_diagonal_ne_zero {p : ℕ} {x : Fin p → ℂ}
    (hx : x ≠ 0) {k : Fin p} (hk : x k ≠ 0) : projectiveKernelCoordinates x k k ≠ 0 := by
  exact div_ne_zero (mul_ne_zero hk ((map_ne_zero (starRingEnd ℂ)).mpr hk))
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))

theorem projectiveKernelCoordinates_ratio {p : ℕ} {x : Fin p → ℂ}
    (hx : x ≠ 0) {k : Fin p} (hk : x k ≠ 0) (j : Fin p) :
    projectiveKernelCoordinates x j k / projectiveKernelCoordinates x k k = normalizeCoordinates k x j := by
  have hn : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hconj : conj (x k) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hk
  unfold projectiveKernelCoordinates normalizeCoordinates
  field_simp

theorem projectiveKernel_injective (p : ℕ) :
    Function.Injective (projectiveKernel : ℙ ℂ (Fin p → ℂ) → Fin p → Fin p → ℂ) := by
  intro q r he
  obtain ⟨k, hk⟩ : ∃ k, q.rep k ≠ 0 := by
    by_contra hh
    push Not at hh
    exact q.rep_nonzero (funext hh)
  have hqr : projectiveKernelCoordinates q.rep = projectiveKernelCoordinates r.rep := he
  have hrk : r.rep k ≠ 0 := by
    intro hzero
    have hh := projectiveKernelCoordinates_diagonal_ne_zero q.rep_nonzero hk
    rw [hqr] at hh
    simp [projectiveKernelCoordinates, hzero] at hh
  have hn : normalizeCoordinates k q.rep = normalizeCoordinates k r.rep := by
    funext j
    rw [← projectiveKernelCoordinates_ratio q.rep_nonzero hk j,
      ← projectiveKernelCoordinates_ratio r.rep_nonzero hrk j, hqr]
  have hq0 : normalizeCoordinates k q.rep ≠ 0 := by
    intro hz
    have hh := congrFun hz k
    simp [normalizeCoordinates, hk] at hh
  have hr0 : normalizeCoordinates k r.rep ≠ 0 := by
    intro hz
    have hh := congrFun hz k
    simp [normalizeCoordinates, hrk] at hh
  calc
    q = Projectivization.mk ℂ (normalizeCoordinates k q.rep) hq0 := by
      rw [projective_mk_normalizeCoordinates k hk q.rep_nonzero, Projectivization.mk_rep]
    _ = Projectivization.mk ℂ (normalizeCoordinates k r.rep) hr0 := by congr 1
    _ = r := by rw [projective_mk_normalizeCoordinates k hrk r.rep_nonzero, Projectivization.mk_rep]

instance projectivizationT2Space (p : ℕ) : T2Space (ℙ ℂ (Fin p → ℂ)) :=
  T2Space.of_injective_continuous (projectiveKernel_injective p) (projectiveKernel_continuous p)

end ModifiedCartan
