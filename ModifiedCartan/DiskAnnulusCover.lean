import ModifiedCartan.DiskStripCover
import ModifiedCartan.AnnulusTopology

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

def diskAnnulusCover (A B : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((((A+B)/2 : ℝ) : ℂ)+(((B-A)/Real.pi : ℝ) : ℂ)*Complex.I*Complex.log (diskCayley z))

theorem diskAnnulusCover_differentiableOn (A B : ℝ) :
    DifferentiableOn ℂ (diskAnnulusCover A B) (disk 1) := by
  have hh := log_diskCayley_differentiableOn
  unfold diskAnnulusCover
  exact (differentiableOn_const _ |>.add ((differentiableOn_const _).mul hh)).cexp

theorem diskAnnulusCover_mapsTo {A B : ℝ} (hAB : A < B) :
    MapsTo (diskAnnulusCover A B) (disk 1) (complexAnnulus (Real.exp A) (Real.exp B)) := by
  intro z hz
  let d := (B-A)/Real.pi
  have hd : 0 < d := div_pos (sub_pos.mpr hAB) Real.pi_pos
  have hdπ : d*Real.pi = B-A := div_mul_cancel₀ _ Real.pi_ne_zero
  obtain ⟨hl,hu⟩ := log_diskCayley_im_bounds hz
  have hl' := mul_lt_mul_of_pos_left hl hd
  have hu' := mul_lt_mul_of_pos_left hu hd
  have hre : ((((A+B)/2 : ℝ) : ℂ)+(d : ℂ)*Complex.I*Complex.log (diskCayley z)).re =
      (A+B)/2-d*(Complex.log (diskCayley z)).im := by simp [Complex.mul_re,Complex.mul_im]; ring
  change Real.exp A < ‖diskAnnulusCover A B z‖ ∧ ‖diskAnnulusCover A B z‖ < Real.exp B
  simp only [diskAnnulusCover,Complex.norm_exp]
  change Real.exp A < Real.exp ((((A+B)/2 : ℝ) : ℂ)+(d : ℂ)*Complex.I*Complex.log (diskCayley z)).re ∧
    Real.exp ((((A+B)/2 : ℝ) : ℂ)+(d : ℂ)*Complex.I*Complex.log (diskCayley z)).re < Real.exp B
  rw [hre]
  constructor <;> apply Real.exp_lt_exp.mpr <;> nlinarith

theorem diskAnnulusCover_surjOn {A B : ℝ} (hAB : A < B) :
    SurjOn (diskAnnulusCover A B) (disk 1) (complexAnnulus (Real.exp A) (Real.exp B)) := by
  intro w hw
  have hw0 : 0 < ‖w‖ := (Real.exp_pos A).trans hw.1
  have hwn : w ≠ 0 := norm_pos_iff.mp hw0
  have hvA : A < (Complex.log w).re := by
    simpa only [Complex.log_re,Real.log_exp] using Real.log_lt_log (Real.exp_pos A) hw.1
  have hvB : (Complex.log w).re < B := by
    simpa only [Complex.log_re,Real.log_exp] using Real.log_lt_log hw0 hw.2
  let c := (A+B)/2
  let d := (B-A)/Real.pi
  have hd : 0 < d := div_pos (sub_pos.mpr hAB) Real.pi_pos
  have hdπ : d*Real.pi = B-A := div_mul_cancel₀ _ Real.pi_ne_zero
  let t : ℂ := (-Complex.I)*((Complex.log w)-(c : ℂ))/(d : ℂ)
  have ht : t.im = -((Complex.log w).re-c)/d := by
    simp [t,div_eq_mul_inv,Complex.mul_im,Complex.mul_re]
    field_simp [hd.ne']
    <;> ring
  have htbound : -(Real.pi/2) < t.im ∧ t.im < Real.pi/2 := by
    rw [ht]
    constructor
    · apply (lt_div_iff₀ hd).mpr
      dsimp [c]
      nlinarith
    · apply (div_lt_iff₀ hd).mpr
      dsimp [c]
      nlinarith
  obtain ⟨z,hz,he⟩ := log_diskCayley_surj_strip htbound
  refine ⟨z,hz,?_⟩
  have hlin : (c : ℂ)+(d : ℂ)*Complex.I*t = Complex.log w := by
    dsimp [t]
    field_simp [Complex.ofReal_ne_zero.mpr hd.ne']
    <;> ring_nf
    <;> simp [Complex.I_sq]
  change Complex.exp ((c : ℂ)+(d : ℂ)*Complex.I*Complex.log (diskCayley z)) = w
  rw [he,hlin,Complex.exp_log hwn]

end ModifiedCartan
