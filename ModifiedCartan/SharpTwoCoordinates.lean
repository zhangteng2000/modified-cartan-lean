import ModifiedCartan.SharpTwoSetup
import ModifiedCartan.DiskSegmentCompact
import ModifiedCartan.Rescaling

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem sharp_two_coordinates {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ} {Ω : Set ℂ}
    (D : SharpTwoSetup A a s Ω) :
    ∃ t : ℕ → ℝ, ∃ ξ : ℕ → ℂ, ∀ n,
      0 ≤ t n ∧ t n ≤ D.q ∧ ‖ξ n‖ = 1 ∧
      ‖D.point 0 n / (D.ρ n : ℂ)‖ ≤ D.r / D.α ∧
      AnalyticOnNhd ℂ (fun z => (D.ρ n : ℂ) *
        diskSegmentMap (D.point 0 n / (D.ρ n : ℂ)) (ξ n) (t n) z) (disk 1) ∧
      MapsTo (fun z => (D.ρ n : ℂ) * diskSegmentMap (D.point 0 n / (D.ρ n : ℂ)) (ξ n) (t n) z)
        (disk 1) (disk (D.ρ n)) ∧
      (D.ρ n : ℂ) * diskSegmentMap (D.point 0 n / (D.ρ n : ℂ)) (ξ n) (t n) ((-t n : ℝ) : ℂ) = D.point 0 n ∧
      (D.ρ n : ℂ) * diskSegmentMap (D.point 0 n / (D.ρ n : ℂ)) (ξ n) (t n) (t n : ℂ) = D.point 1 n := by
  have hα : 0 < D.α := D.r_pos.trans D.r_lt
  have hρ0 : ∀ n, 0 < D.ρ n := fun n => hα.trans_le (D.radius n).1
  have hρ1 : ∀ n, D.ρ n < 1 := fun n => (D.radius n).2.trans (D.β_lt.trans D.v_lt)
  have hdist := fun n => D.pseudodistance (D.ρ n) ⟨(D.radius n).1, (hρ1 n).le⟩
    (D.point 0 n) (D.point_mem 0 n) (D.point 1 n) (D.point_mem 1 n)
  choose t ξ ht htq hξ hleft hright using fun n =>
    exists_diskSegmentMap (hdist n).1 (hdist n).2.1 D.q_pos.le (hdist n).2.2
  refine ⟨t, ξ, ?_⟩
  intro n
  have htn : |t n| < 1 := by rw [abs_of_nonneg (ht n)]; exact (htq n).trans_lt (D.q_lt.trans sharpRadius_lt_one)
  have han : ‖D.point 0 n / (D.ρ n : ℂ)‖ < 1 := by simpa [disk] using (hdist n).1
  have hcoeff : ‖D.point 0 n / (D.ρ n : ℂ)‖ ≤ D.r / D.α := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ0 n)]
    exact (div_le_div_of_nonneg_right
      (show ‖D.point 0 n‖ ≤ D.r by simpa only [mem_closedBall, dist_zero_right] using D.contained (D.point_mem 0 n))
      (hρ0 n).le).trans (div_le_div_of_nonneg_left D.r_pos.le hα (D.radius n).1)
  refine ⟨ht n, htq n, hξ n, hcoeff, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [Pi.mul_def] using analyticAt_const.mul (diskSegmentMap_analytic han (hξ n) htn z hz)
  · intro z hz
    simpa only [mul_one] using (real_scale_mem_disk (hρ0 n)).mpr (diskSegmentMap_mem_disk han (hξ n) htn hz)
  · rw [hleft n, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hρ0 n).ne')]
  · rw [hright n, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hρ0 n).ne')]

theorem sharp_two_parameter_subsequence {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ} {Ω : Set ℂ}
    (D : SharpTwoSetup A a s Ω) {t : ℕ → ℝ} {ξ : ℕ → ℂ}
    (ht : ∀ n, t n ∈ Icc 0 D.q) (hξ : ∀ n, ‖ξ n‖ = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x y : ℂ, ∃ R T : ℝ, ∃ X : ℂ,
      x ∈ D.L ∧ y ∈ D.L ∧ R ∈ Icc D.α D.β ∧ T ∈ Icc 0 D.q ∧ ‖X‖ = 1 ∧
      Tendsto (fun n => D.point 0 (φ n)) atTop (𝓝 x) ∧
      Tendsto (fun n => D.point 1 (φ n)) atTop (𝓝 y) ∧
      Tendsto (fun n => D.ρ (φ n)) atTop (𝓝 R) ∧
      Tendsto (fun n => t (φ n)) atTop (𝓝 T) ∧
      Tendsto (fun n => ξ (φ n)) atTop (𝓝 X) := by
  let K : Set (ℂ × ℂ × ℝ × ℝ × ℂ) := D.L ×ˢ D.L ×ˢ Icc D.α D.β ×ˢ Icc 0 D.q ×ˢ sphere 0 1
  have hK : IsCompact K := D.compact.prod (D.compact.prod
    (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_sphere (0 : ℂ) 1))))
  have hmem : ∀ n, (D.point 0 n, D.point 1 n, D.ρ n, t n, ξ n) ∈ K := by
    intro n
    exact ⟨D.point_mem 0 n, D.point_mem 1 n, ⟨(D.radius n).1, (D.radius n).2.le⟩,
      ht n, by simpa only [mem_sphere, dist_zero_right] using hξ n⟩
  obtain ⟨p, hp, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hlim' : Tendsto (fun n => (D.point 0 (φ n), D.point 1 (φ n), D.ρ (φ n), t (φ n), ξ (φ n)))
      atTop (𝓝 p) := hlim
  have hX : Tendsto (fun n => ξ (φ n)) atTop (𝓝 p.2.2.2.2) :=
    ((show Continuous (fun v : ℂ × ℂ × ℝ × ℝ × ℂ => v.2.2.2.2) by fun_prop).tendsto p).comp hlim'
  have hT : Tendsto (fun n => t (φ n)) atTop (𝓝 p.2.2.2.1) :=
    ((show Continuous (fun v : ℂ × ℂ × ℝ × ℝ × ℂ => v.2.2.2.1) by fun_prop).tendsto p).comp hlim'
  have hR : Tendsto (fun n => D.ρ (φ n)) atTop (𝓝 p.2.2.1) :=
    ((show Continuous (fun v : ℂ × ℂ × ℝ × ℝ × ℂ => v.2.2.1) by fun_prop).tendsto p).comp hlim'
  have hy : Tendsto (fun n => D.point 1 (φ n)) atTop (𝓝 p.2.1) :=
    ((show Continuous (fun v : ℂ × ℂ × ℝ × ℝ × ℂ => v.2.1) by fun_prop).tendsto p).comp hlim'
  have hx : Tendsto (fun n => D.point 0 (φ n)) atTop (𝓝 p.1) :=
    ((show Continuous (fun v : ℂ × ℂ × ℝ × ℝ × ℂ => v.1) by fun_prop).tendsto p).comp hlim'
  exact ⟨φ, hφ, p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2,
    hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
    by simpa only [mem_sphere, dist_zero_right] using hp.2.2.2.2,
    hx, hy, hR, hT, hX⟩

end ModifiedCartan
