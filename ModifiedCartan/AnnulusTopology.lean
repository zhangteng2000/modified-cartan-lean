import ModifiedCartan.CartanMergeAnnulus
import ModifiedCartan.CartanThreeDomain
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

theorem complexAnnulus_isOpen (a b : ℝ) : IsOpen (complexAnnulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem complexAnnulus_nonempty {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (complexAnnulus a b).Nonempty := by
  have hm : 0 < (a+b)/2 := by linarith
  refine ⟨((a+b)/2 : ℝ), ?_⟩
  change a < ‖(((a+b)/2 : ℝ) : ℂ)‖ ∧ ‖(((a+b)/2 : ℝ) : ℂ)‖ < b
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  constructor <;> linarith

theorem complexAnnulus_preconnected {a b : ℝ} (ha : 0 ≤ a) :
    IsPreconnected (complexAnnulus a b) := by
  have he : complexAnnulus a b = (fun v : ℝ × ℂ => v.1 • v.2) ''
      (Ioo a b ×ˢ sphere (0 : ℂ) 1) := by
    ext z
    constructor
    · intro hz
      have hn : 0 < ‖z‖ := ha.trans_lt hz.1
      let u : ℂ := ‖z‖⁻¹ • z
      have hu : u ∈ sphere (0 : ℂ) 1 := by
        simp [u, norm_inv, hn.ne']
      refine ⟨(‖z‖, u), ⟨hz, hu⟩, ?_⟩
      dsimp [u]
      rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hn.ne'), one_mul]
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      have hr0 : 0 < r := ha.trans_lt hr.1
      have hun : ‖u‖ = 1 := by simpa using hu
      change a < ‖r • u‖ ∧ ‖r • u‖ < b
      simpa [norm_smul, hun, abs_of_pos hr0] using hr
  rw [he]
  apply (isPreconnected_Ioo.prod
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) (0 : ℂ) 1)).image
  fun_prop

end ModifiedCartan
