import ModifiedCartan.CauchyBounds
import Mathlib.Analysis.Complex.BorelCaratheodory

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

/-- Cauchy estimates from an upper bound for the real part, with the imaginary
constant removed before applying Borel-Carathéodory. -/
theorem iteratedDeriv_bound_of_real_part {f : ℂ → ℂ} {T r M : ℝ}
    (hr : 0 ≤ r) (hrT : r < T) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (disk T)) (hf0 : f 0 = 0)
    (hre : ∀ z ∈ disk T, (f z).re ≤ M) (j : ℕ) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖iteratedDeriv j f z‖ ≤ (j.factorial : ℝ) / ((T - r) / 2) ^ j *
      (2 * M * ((T + r) / 2) / (T - (T + r) / 2)) := by
  let B := (T + r) / 2
  let δ := (T - r) / 2
  have hT : 0 < T := hr.trans_lt hrT
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hBT : B < T := by dsimp [B]; linarith
  have hsub : closedBall z δ ⊆ closedBall (0 : ℂ) B := by
    intro w hw
    have hd : ‖w - z‖ ≤ δ := by simpa [mem_closedBall, dist_eq_norm] using hw
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      calc
        _ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hWB : ‖w‖ ≤ B := by dsimp [B, δ] at *; linarith
    simpa using hWB
  have hfb : ∀ w ∈ closedBall (0 : ℂ) B, ‖f w‖ ≤ 2 * M * B / (T - B) := by
    intro w hw
    have hn : ‖w‖ ≤ B := by simpa using hw
    have hwT : w ∈ disk T := closedBall_subset_ball hBT hw
    apply (Complex.borelCaratheodory_zero hM hf (fun w hw => hre w hw) hT hwT hf0).trans
    apply div_le_div₀
    · positivity
    · exact mul_le_mul_of_nonneg_left hn (by positivity)
    · linarith
    · linarith
  have hreg : DifferentiableOn ℂ f (closure (ball z δ)) := by
    rw [closure_ball _ hδ.ne']
    exact hf.mono (hsub.trans (closedBall_subset_ball hBT))
  convert Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hδ hreg.diffContOnCl
    (fun w hw => hfb w (hsub (sphere_subset_closedBall hw))) using 1
  dsimp [δ, B]
  ring

end ModifiedCartan
