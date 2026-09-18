import ModifiedCartan.VanishingDerivative
import ModifiedCartan.TwoWronskian
import ModifiedCartan.ZeroFreeAnnulus

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem two_term_quotient_vanishingDerivative {a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ}
    {U : Set ℂ} (hU1 : U ⊆ disk 1)
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    (hsne : ∀ z ∈ U, s z ≠ 0)
    (hW : CompactConvergence (fun n => wronskian (fun i => a i n)) 0 U) :
    LocallyVanishingDerivative (fun n z => a 0 n z / (∑ i, a i n z)) U := by
  have hs := compactConvergence_holomorphic isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
  intro K hKU hK ε hε
  have hK1 := hKU.trans hU1
  obtain ⟨c, hc, hlow⟩ := compactConvergence_eventually_lower_bound hsum hK1 hK
    (hs.continuousOn.mono hK1) (fun z hz => hsne z (hKU hz))
  have hεc : 0 < ε * c ^ 2 := mul_pos hε (sq_pos_of_pos hc)
  filter_upwards [hlow, Metric.tendstoUniformlyOn_iff.mp (hW K hKU hK) (ε * c ^ 2) hεc] with n hn hWn
  have hdiff : ∀ i z, z ∈ K → DifferentiableAt ℂ (a i n) z := fun i z hz =>
    (ha i n z (hK1 hz)).differentiableAt (isOpen_ball.mem_nhds (hK1 hz))
  have hnonzero : ∀ z ∈ K, (∑ i, a i n z) ≠ 0 := fun z hz =>
    norm_pos_iff.mp (hc.trans_le (hn z hz))
  constructor
  · intro z hz
    apply (hdiff 0 z hz).div
    · exact DifferentiableAt.fun_sum (fun i _ => hdiff i z hz)
    · exact hnonzero z hz
  · intro z hz
    have hsneq : a 0 n z + a 1 n z ≠ 0 := by simpa only [Fin.sum_univ_two] using hnonzero z hz
    have hder := deriv_two_term_quotient (fun i => hdiff i z hz) hsneq
    simp only [Fin.sum_univ_two]
    rw [hder, norm_div, norm_neg, norm_pow]
    have hlower : c ≤ ‖a 0 n z + a 1 n z‖ := by simpa only [Fin.sum_univ_two] using hn z hz
    apply (div_le_iff₀ (sq_pos_of_pos (hc.trans_le hlower))).mpr
    have hb : ‖wronskian (fun i => a i n) z‖ < ε * c ^ 2 := by simpa only [Pi.zero_apply, dist_zero_left] using hWn z hz
    exact hb.le.trans (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hc.le (norm_nonneg _)).mpr hlower) hε.le)

/-- A reusable final contradiction: a vanishing derivative cannot connect
moving endpoint values with distinct limits in a connected open domain. -/
theorem vanishingDerivative_endpoint_contradiction {f : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyVanishingDerivative f U) (hU : IsOpen U) (hconn : IsPreconnected U)
    {x y : ℕ → ℂ} {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U)
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b))
    (hzero : Tendsto (fun n => f n (x n)) atTop (𝓝 0))
    (hone : Tendsto (fun n => f n (y n)) atTop (𝓝 1)) : False := by
  have hdiff := vanishingDerivative_moving_difference hf hU hconn ha hb hx hy
  have hdiff' : Tendsto (fun n => f n (y n) - f n (x n)) atTop (𝓝 1) := by
    simpa only [sub_zero] using hone.sub hzero
  exact zero_ne_one (tendsto_nhds_unique hdiff hdiff')

end ModifiedCartan
