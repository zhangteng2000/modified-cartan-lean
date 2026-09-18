import ModifiedCartan.WronskianDifferentiation
import ModifiedCartan.MatrixAnalytic

noncomputable section
set_option autoImplicit false
open Set
namespace ModifiedCartan

def minorJetMatrix {m : ℕ} (g : Fin (m + 1) → ℂ → ℂ) (z : ℂ) :
    Matrix (Fin m) (Fin m) ℂ := .of fun i j => iteratedDeriv (i : ℕ) (g j.castSucc) z

def lastJetVector {m : ℕ} (g : Fin (m + 1) → ℂ → ℂ) (z : ℂ) : Fin m → ℂ :=
  fun i => iteratedDeriv (i : ℕ) (g (Fin.last m)) z

def wronskianCoefficient {m : ℕ} (g : Fin (m + 1) → ℂ → ℂ) (j : Fin m) (z : ℂ) : ℂ :=
  ((minorJetMatrix g z)⁻¹.mulVec (lastJetVector g z)) j

theorem wronskianCoefficient_relation {m : ℕ} (g : Fin (m + 1) → ℂ → ℂ) {z : ℂ}
    (hV : wronskian (fun j : Fin m => g j.castSucc) z ≠ 0) (i : Fin m) :
    ∑ j, iteratedDeriv (i : ℕ) (g j.castSucc) z * wronskianCoefficient g j z =
      iteratedDeriv (i : ℕ) (g (Fin.last m)) z := by
  have hunit : IsUnit (minorJetMatrix g z).det := isUnit_iff_ne_zero.mpr hV
  have he := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M.mulVec (lastJetVector g z))
    (Matrix.mul_nonsing_inv (minorJetMatrix g z) hunit)
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at he
  exact congrFun he i

theorem wronskianCoefficient_analyticAt {m : ℕ} {g : Fin (m + 1) → ℂ → ℂ} {U : Set ℂ}
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) {z : ℂ} (hz : z ∈ U)
    (hV : wronskian (fun j : Fin m => g j.castSucc) z ≠ 0) (j : Fin m) :
    AnalyticAt ℂ (wronskianCoefficient g j) z := by
  unfold wronskianCoefficient Matrix.mulVec dotProduct
  apply Finset.analyticAt_fun_sum
  intro i _
  apply AnalyticAt.mul
  · exact matrix_inv_entry_analyticAt
      (fun i j => iteratedDeriv_analyticOnNhd (hg j.castSucc) i z hz) hV j i
  · exact iteratedDeriv_analyticOnNhd (hg (Fin.last m)) i z hz

/-- The actual coefficients Y⁻¹v satisfy the manuscript's derivative identity. -/
theorem wronskianCoefficient_deriv {n : ℕ} {g : Fin (n + 2) → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) {z : ℂ} (hz : z ∈ U)
    (hV : wronskian (fun j : Fin (n + 1) => g j.castSucc) z ≠ 0) (j : Fin (n + 1)) :
    deriv (wronskianCoefficient g j) z = (minorJetMatrix g z)⁻¹ j (Fin.last n) *
      (wronskian g z / wronskian (fun j : Fin (n + 1) => g j.castSucc) z) := by
  classical
  let V := U ∩ (wronskian (fun j : Fin (n + 1) => g j.castSucc)) ⁻¹' ({0} : Set ℂ)ᶜ
  have hVopen : IsOpen V := (wronskian_analyticOnNhd (fun j => hg j.castSucc)).continuousOn.isOpen_inter_preimage
    hU isClosed_singleton.isOpen_compl
  have hzV : z ∈ V := ⟨hz, hV⟩
  have hd : ∀ j, DifferentiableOn ℂ (wronskianCoefficient g j) V := by
    intro j w hw
    exact (wronskianCoefficient_analyticAt hg hw.1 hw.2 j).differentiableAt.differentiableWithinAt
  have hsys := wronskian_coefficient_derivative_system hVopen (fun j => (hg j).mono inter_subset_left)
    hd (fun i w hw => wronskianCoefficient_relation g hw.2 i) hzV hV
  let M := minorJetMatrix g z
  let v : Fin (n + 1) → ℂ := fun i => deriv (wronskianCoefficient g i) z
  let r : ℂ := wronskian g z / wronskian (fun j : Fin (n + 1) => g j.castSucc) z
  have he : M.mulVec v = Pi.single (Fin.last n) r := by
    ext i
    simpa [M, v, r, minorJetMatrix, Matrix.mulVec, dotProduct, Pi.single_apply] using hsys i
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hV
  have hi := congrArg (fun v => M⁻¹.mulVec v) he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hunit, Matrix.one_mulVec] at hi
  have hij := congrFun hi j
  simpa [M, v, r, Matrix.mulVec, dotProduct, Pi.single_apply] using hij

end ModifiedCartan
