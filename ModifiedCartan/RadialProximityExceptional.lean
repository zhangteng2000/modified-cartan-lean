import ModifiedCartan.CartanRadialExceptional
import ModifiedCartan.ProximityGrowth

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory intervalIntegral
namespace ModifiedCartan

theorem cartan_small_value_radii_local {a b c T R : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c)
    (haT : a < T) (hcT : c < T) (hTR : T < R) (hR1 : R < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℂ → ℂ) (t δ : ℝ) (w : ℂ),
      DifferentiableOn ℂ F (disk 1) → (∀ z ∈ sphere (0 : ℂ) R, ‖F z‖ ≤ 1) →
      0 < t → t ≤ 1 → 0 < δ → ‖w‖ ≤ a → t ≤ ‖F w‖ →
      volume (radialSmallValueSet F b c (K*(1-Real.log t)/δ)) ≤ ENNReal.ofReal δ := by
  obtain ⟨K,hK,h⟩ := cartan_integrable_radial_loss_local ha hb hbc haT hcT hTR hR1
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


/-- A logarithmic upper bound on one outer circle and one nonzero inner
anchor control the outer measure of all bad concentric circles. -/
theorem cartan_small_value_radii_log_bound {a b c T R : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c)
    (haT : a < T) (hcT : c < T) (hTR : T < R) (hR1 : R < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℂ → ℂ) (S B δ : ℝ),
      DifferentiableOn ℂ F (disk 1) → 0 ≤ S → 0 ≤ B → 0 < δ →
      (∀ z ∈ sphere (0 : ℂ) R, ‖F z‖ ≤ Real.exp S) →
      (∃ w : ℂ, ‖w‖ ≤ a ∧ F w ≠ 0 ∧ -B ≤ Real.log ‖F w‖) →
      volume (radialSmallValueSet F b c (K*(1+B+S)/δ)) ≤ ENNReal.ofReal δ := by
  obtain ⟨K,hK,h⟩ := cartan_small_value_radii_local ha hb hbc haT hcT hTR hR1
  refine ⟨K,hK,?_⟩
  intro F S B δ hF hS hB hδ hupper hanchor
  obtain ⟨w,hw,hn,hlog⟩ := hanchor
  let G : ℂ → ℂ := fun z => (Real.exp (-S) : ℂ)*F z
  have hc : ‖(Real.exp (-S) : ℂ)‖ = Real.exp (-S) := by
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos (-S)).le]
  have hG : DifferentiableOn ℂ G (disk 1) := (differentiableOn_const _).mul hF
  have hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖G z‖ ≤ 1 := by
    intro z hz
    dsimp [G]
    rw [norm_mul,hc]
    have hh := mul_le_mul_of_nonneg_left (hupper z hz) (Real.exp_pos (-S)).le
    simpa [← Real.exp_add] using hh
  have ht : Real.exp (-B-S) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hanchorG : Real.exp (-B-S) ≤ ‖G w‖ := by
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (norm_pos_iff.mpr hn)] at he
    dsimp [G]
    rw [norm_mul,hc]
    calc
      _ = Real.exp (-S)*Real.exp (-B) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
  have hsmall := h G (Real.exp (-B-S)) δ w hG hbound (Real.exp_pos _) ht hδ hw hanchorG
  have heq : K*(1-Real.log (Real.exp (-B-S)))/δ = K*(1+B+S)/δ := by rw [Real.log_exp]; ring
  rw [heq] at hsmall
  apply (measure_mono (show radialSmallValueSet F b c (K*(1+B+S)/δ) ⊆
      radialSmallValueSet G b c (K*(1+B+S)/δ) from ?_)).trans hsmall
  rintro ρ ⟨hρ,z,hz,hbad⟩
  refine ⟨hρ,z,hz,?_⟩
  by_cases hnz : F z = 0
  · exact Or.inl (by simp [G,hnz])
  · right
    have hl : K*(1+B+S)/δ < -Real.log ‖F z‖ := hbad.resolve_left hnz
    have he : Real.log ‖G z‖ = -S+Real.log ‖F z‖ := by
      dsimp [G]
      rw [norm_mul,hc,Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hnz),Real.log_exp]
    rw [he]
    linarith


theorem radialSmallValueSet_antitone {F : ℂ → ℂ} {b c L K : ℝ} (hLK : L ≤ K) :
    radialSmallValueSet F b c K ⊆ radialSmallValueSet F b c L := by
  rintro ρ ⟨hρ,z,hz,hbad⟩
  refine ⟨hρ,z,hz,hbad.imp id (fun hh => hLK.trans_lt hh)⟩

/-- Uniform radial small-value control from an outer proximity mean and an
inner logarithmic anchor. The radius used for the proximity mean may vary. -/
theorem cartan_small_value_radii_proximity {a b c T R r₀ : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c)
    (haT : a < T) (hcT : c < T) (hTR : T < R) (hRr : R < r₀) (hr1 : r₀ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℂ → ℂ) (r B δ : ℝ),
      DifferentiableOn ℂ F (disk 1) → r₀ ≤ r → r < 1 → 0 ≤ B → 0 < δ →
      (∃ w : ℂ, ‖w‖ ≤ a ∧ F w ≠ 0 ∧ -B ≤ Real.log ‖F w‖) →
      volume (radialSmallValueSet F b c (K*(1+B+proximityMean F r)/δ)) ≤ ENNReal.ofReal δ := by
  have hR : 0 < R := (ha.trans haT).trans hTR
  obtain ⟨K,hK,h⟩ := cartan_small_value_radii_log_bound ha hb hbc haT hcT hTR (hRr.trans hr1)
  let Q := (1+R)/(r₀-R)
  let C := max 1 Q
  have hQ : 0 ≤ Q := div_nonneg (by linarith) (by linarith)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  refine ⟨K*C,mul_pos hK hC,?_⟩
  intro F r B δ hF hr hr' hB hδ haF
  have hm : 0 ≤ proximityMean F r := ValueDistribution.proximity_nonneg r
  have hq : (r+R)/(r-R) ≤ Q := by
    apply (div_le_div_iff₀ (by linarith : 0 < r-R) (by linarith : 0 < r₀-R)).mpr
    exact (mul_le_mul_of_nonneg_left (by linarith : r₀-R ≤ r-R) (by linarith : 0 ≤ r+R)).trans
      (mul_le_mul_of_nonneg_right (by linarith : r+R ≤ 1+R) (by linarith : 0 ≤ r-R))
  have hupper : ∀ z ∈ sphere (0 : ℂ) R, ‖F z‖ ≤ Real.exp (Q*proximityMean F r) := by
    intro z hz
    have hzR : ‖z‖ ≤ R := (by simpa using hz : ‖z‖ = R).le
    exact (norm_le_exp_proximity_on_closedBall hR.le (hRr.trans_le hr)
      (hF.analyticOnNhd isOpen_ball |>.mono (closedBall_subset_ball hr')) hzR).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hq hm))
  have hsmall := h F (Q*proximityMean F r) B δ hF (mul_nonneg hQ hm) hB hδ hupper haF
  have hcoeff : 1+B+Q*proximityMean F r ≤ C*(1+B+proximityMean F r) := by
    calc
      _ ≤ C*(1+B)+C*proximityMean F r := add_le_add
        (le_mul_of_one_le_left (by linarith) (le_max_left _ _))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hm)
      _ = _ := by ring
  have hthreshold : K*(1+B+Q*proximityMean F r)/δ ≤ K*C*(1+B+proximityMean F r)/δ := by
    apply div_le_div_of_nonneg_right _ hδ.le
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcoeff hK.le
  exact (measure_mono (radialSmallValueSet_antitone hthreshold)).trans hsmall

end ModifiedCartan
