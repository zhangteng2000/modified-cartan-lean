import ModifiedCartan.RadialLoss

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory intervalIntegral
namespace ModifiedCartan

/-- Radii on whose circle there is a zero or a logarithmic value below the
prescribed lower bound. Measurability of this projection is not assumed. -/
def radialSmallValueSet (F : ℂ → ℂ) (b c L : ℝ) : Set ℝ :=
  {ρ | ρ ∈ Icc b c ∧ ∃ z : ℂ, ‖z‖ = ρ ∧ (F z = 0 ∨ L < -Real.log ‖F z‖)}

/-- Markov's inequality controls the actual small-value circles, including
all circles passing through zeros, from an almost-everywhere radial loss. -/
theorem radialSmallValueSet_measure_le {F : ℂ → ℂ} {E : ℝ → ℝ} {b c L : ℝ}
    (hbc : b ≤ c) (hL : 0 < L) (hi : IntervalIntegrable E volume b c)
    (hn : ∀ ρ ∈ Icc b c, 0 ≤ E ρ)
    (he : ∀ᵐ ρ ∂volume.restrict (Icc b c),
      ∀ z : ℂ, ‖z‖ = ρ → F z ≠ 0 ∧ -Real.log ‖F z‖ ≤ E ρ) :
    volume (radialSmallValueSet F b c L) ≤ ENNReal.ofReal ((∫ ρ in b..c, E ρ) / L) := by
  let μ := volume.restrict (Icc b c)
  have hm : μ (radialSmallValueSet F b c L) ≤ μ {ρ | 1 ≤ E ρ / L} := by
    apply measure_mono_ae
    filter_upwards [he] with ρ hρ
    rintro ⟨hρbc,z,hz,hbad⟩
    have hlow := hρ z hz
    have hLE : L ≤ E ρ := by
      rcases hbad with hnz | hlog
      · exact False.elim (hlow.1 hnz)
      · exact hlog.le.trans hlow.2
    exact (one_le_div hL).mpr hLE
  have hi' : Integrable E μ := (intervalIntegrable_iff_integrableOn_Icc_of_le hbc).mp hi
  have hnonneg : 0 ≤ᵐ[μ] (fun ρ => E ρ / L) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with ρ hρ
    exact div_nonneg (hn ρ hρ) hL.le
  have hmark := (hi'.div_const L).measure_le_integral hnonneg
    (s := {ρ | 1 ≤ E ρ/L}) (fun _ h => h)
  have hset : radialSmallValueSet F b c L ∩ Icc b c = radialSmallValueSet F b c L :=
    inter_eq_self_of_subset_left (fun _ h => h.1)
  have hleft : μ (radialSmallValueSet F b c L) = volume (radialSmallValueSet F b c L) := by
    dsimp [μ]
    rw [Measure.restrict_apply' measurableSet_Icc,hset]
  rw [hleft] at hm
  apply (hm.trans hmark).trans_eq
  congr 1
  simp only [div_eq_mul_inv,MeasureTheory.integral_mul_const]
  dsimp [μ]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hbc]

/-- A bounded holomorphic function with one quantitative nonzero anchor is
bounded below on every circle outside a set of arbitrarily small radial length. -/
theorem cartan_small_value_radii {a b c T R : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c)
    (haT : a < T) (hcT : c < T) (hTR : T < R) (hR1 : R < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℂ → ℂ) (t δ : ℝ) (w : ℂ),
      DifferentiableOn ℂ F (disk 1) → (∀ z ∈ disk 1, ‖F z‖ ≤ 1) →
      0 < t → t ≤ 1 → 0 < δ → ‖w‖ ≤ a → t ≤ ‖F w‖ →
      volume (radialSmallValueSet F b c (K*(1-Real.log t)/δ)) ≤ ENNReal.ofReal δ := by
  obtain ⟨K,hK,h⟩ := cartan_integrable_radial_loss ha hb hbc haT hcT hTR hR1
  refine ⟨K,hK,?_⟩
  intro F t δ w hF hbF ht ht1 hδ hw hwF
  obtain ⟨E,hi,hn,hint,he⟩ := h F t w hF hbF ht ht1 hw hwF
  have hlt : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have hL : 0 < K*(1-Real.log t)/δ := div_pos (mul_pos hK (by linarith)) hδ
  apply (radialSmallValueSet_measure_le hbc.le hL hi hn he).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hL).mpr
  have hcancel : δ * (K*(1-Real.log t)/δ) = K*(1-Real.log t) := mul_div_cancel₀ _ hδ.ne'
  rw [hcancel]
  linarith

end ModifiedCartan
