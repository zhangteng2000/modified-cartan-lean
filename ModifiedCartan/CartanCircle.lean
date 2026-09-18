import ModifiedCartan.BlaschkeDecomposition
import ModifiedCartan.RadialLog
import ModifiedCartan.CartanAux

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Metric Set Real
namespace ModifiedCartan

theorem blaschkeFactor_log_lower {R ρ : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    {a z : ℂ} (ha : ‖a‖ < R) (hz : ‖z‖ = ρ) (hρ : ρ ≤ R) (hne : ρ ≠ ‖a‖) :
    0 < ‖blaschkeFactor R a z‖ ∧
      -radialLog ‖a‖ ρ ≤ Real.log ‖blaschkeFactor R a z‖ := by
  have hl := blaschkeFactor_radial_lower hR hR1 ha (hz.trans_le hρ)
  rw [hz] at hl
  have hp : 0 < |ρ - ‖a‖| / 2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  refine ⟨hp.trans_le hl, ?_⟩
  have hlog := Real.log_le_log hp hl
  rw [Real.log_div (abs_pos.mpr (sub_ne_zero.mpr hne)).ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_abs] at hlog
  dsimp [radialLog]
  linarith

theorem cartan_circle_at_point {a b c T R : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcT : c < T) (hTR : T < R) (hR1 : R < 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (F : ℂ → ℂ) (t : ℝ) (w : ℂ),
      DifferentiableOn ℂ F (disk 1) → (∀ z ∈ disk 1, ‖F z‖ ≤ 1) →
      0 < t → t ≤ 1 → ‖w‖ ≤ a → t ≤ ‖F w‖ →
      ∃ ρ : ℝ, b < ρ ∧ ρ < c ∧ ∀ z : ℂ, ‖z‖ = ρ → t ^ γ ≤ ‖F z‖ := by
  have haT : a < T := hab.trans (hbc.trans hcT)
  have haR : a < R := haT.trans hTR
  have hc : 0 < c := ha.trans (hab.trans hbc)
  have hT : 0 < T := hc.trans hcT
  have hR : 0 < R := hT.trans hTR
  obtain ⟨q₀, hq₀, hq₀1, hqbound⟩ := blaschkeFactor_uniform_bound hT.le ha.le hTR haR
  let q := (q₀ + 1) / 2
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hq₀q : q₀ ≤ q := by dsimp [q]; linarith
  let C := (Real.log 2 + 4) / (c - b)
  let L := -Real.log q
  have hC : 0 < C := div_pos (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]) (by linarith)
  have hL : 0 < L := neg_pos.mpr (Real.log_neg hq hq1)
  let γ := harnackPower T a c + C / L
  have hγ : 0 < γ := add_pos (harnackPower_pos ha.le hc.le haT hcT) (div_pos hC hL)
  refine ⟨γ, hγ, ?_⟩
  intro F t w hF hbound ht _ht1 hw htF
  have hwR : w ∈ closedBall (0 : ℂ) R := by simpa using hw.trans haR.le
  have hRsub : closedBall (0 : ℂ) R ⊆ disk 1 := closedBall_subset_ball hR1
  have hFw : F w ≠ 0 := norm_pos_iff.mp (ht.trans_le htF)
  obtain ⟨s, m, Q, hs, hQ, hQnz, hQbound, hfact⟩ :=
    bounded_blaschke_factorization hF hbound (hRsub hwR) hFw hT.le hTR hR1
  let N : ℕ := ∑ v ∈ s, m v
  have hprodq : ‖∏ v ∈ s, blaschkeFactor R v w ^ m v‖ ≤ q ^ N := by
    simp only [norm_prod, norm_pow]
    dsimp [N]
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _)
    intro v hv
    exact pow_le_pow_left₀ (norm_nonneg _) ((hqbound v w (hs v hv).1 hw).trans hq₀q) _
  have hprod1 : ‖∏ v ∈ s, blaschkeFactor R v w ^ m v‖ ≤ 1 :=
    hprodq.trans (pow_le_one₀ hq.le hq1.le)
  have htq : t ≤ q ^ N := by
    apply htF.trans
    rw [hfact w hwR, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hQbound w hwR)).trans hprodq
  have htQ : t ≤ ‖Q w‖ := by
    apply htF.trans
    rw [hfact w hwR, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hprod1
  have hN : (N : ℝ) ≤ (-Real.log t) / L := power_bound_zero_count ht hq hq1 htq
  obtain ⟨ρ, hρ, hρne, hsum⟩ := radialLog_select_radius_with_weights s (fun v : ℂ => ‖v‖) m
    (ha.le.trans hab.le) hbc (hcT.le.trans (hTR.le.trans hR1.le))
    (fun v hv => ⟨norm_nonneg _, (hs v hv).1.trans (hTR.le.trans hR1.le)⟩)
    (fun v hv => (hs v hv).2)
  refine ⟨ρ, hρ.1, hρ.2, ?_⟩
  intro z hz
  have hzT : z ∈ closedBall (0 : ℂ) T := by simpa [hz] using hρ.2.le.trans hcT.le
  have hzR := closedBall_subset_closedBall hTR.le hzT
  have hB : ∀ v ∈ s, 0 < ‖blaschkeFactor R v z‖ ∧
      -radialLog ‖v‖ ρ ≤ Real.log ‖blaschkeFactor R v z‖ := by
    intro v hv
    exact blaschkeFactor_log_lower hR hR1.le ((hs v hv).1.trans_lt hTR) hz
      (hρ.2.le.trans (hcT.le.trans hTR.le)) (hρne v hv)
  have hQlog : harnackPower T a c * Real.log t ≤ Real.log ‖Q z‖ :=
    zero_free_log_lower ha.le hc.le haT hcT
      (hQ.mono (closedBall_subset_ball (hTR.trans hR1))) hQnz
      (fun v hv => hQbound v (closedBall_subset_closedBall hTR.le hv))
      hw (hz.trans_le hρ.2.le) ht htQ
  have hBnz : ∀ v ∈ s, ‖blaschkeFactor R v z‖ ^ m v ≠ 0 :=
    fun v hv => pow_ne_zero _ (hB v hv).1.ne'
  have hQnorm : 0 < ‖Q z‖ := norm_pos_iff.mpr (hQnz z hzT)
  have hFnorm : 0 < ‖F z‖ := by
    rw [hfact z hzR, norm_mul, norm_prod]
    simp only [norm_pow]
    exact mul_pos (Finset.prod_pos (fun v hv => pow_pos (hB v hv).1 _)) hQnorm
  have hlogF : Real.log ‖F z‖ =
      (∑ v ∈ s, (m v : ℝ) * Real.log ‖blaschkeFactor R v z‖) + Real.log ‖Q z‖ := by
    rw [hfact z hzR, norm_mul, norm_prod]
    simp only [norm_pow]
    rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr hBnz) hQnorm.ne', Real.log_prod hBnz]
    simp only [Real.log_pow]
  have hlogB : -(C * (N : ℝ)) ≤ ∑ v ∈ s, (m v : ℝ) * Real.log ‖blaschkeFactor R v z‖ := by
    have hle := Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hB v hv).2 (Nat.cast_nonneg (m v)))
    simp only [mul_neg, Finset.sum_neg_distrib] at hle
    change (∑ v ∈ s, (m v : ℝ) * radialLog ‖v‖ ρ) ≤ C * (N : ℝ) at hsum
    linarith
  have hCN := mul_le_mul_of_nonneg_left hN hC.le
  have hlogall : γ * Real.log t ≤ Real.log ‖F z‖ := by
    rw [hlogF]
    have he : C * (-Real.log t / L) = -(C / L) * Real.log t := by ring
    rw [he] at hCN
    dsimp [γ]
    nlinarith only [hCN, hlogB, hQlog]
  rw [Real.rpow_def_of_pos ht]
  calc
    Real.exp (Real.log t * γ) ≤ Real.exp (Real.log ‖F z‖) :=
      Real.exp_le_exp.mpr (by simpa only [mul_comm] using hlogall)
    _ = ‖F z‖ := Real.exp_log hFnorm

/-- Full manuscript Lemma `lem:cartan-circle`, with the original power dependence. -/
theorem cartanCircleEstimate_proved : CartanCircleEstimate := by
  intro a b c ha hab hbc hc1
  let T := (c + 1) / 2
  let R := (T + 1) / 2
  have hcT : c < T := by dsimp [T]; linarith
  have hTR : T < R := by dsimp [R, T]; linarith
  have hR1 : R < 1 := by dsimp [R, T]; linarith
  obtain ⟨γ, hγ, hmain⟩ := cartan_circle_at_point ha hab hbc hcT hTR hR1
  refine ⟨γ, hγ, ?_⟩
  intro F t hF hbound ht ht1 htmax
  have ha1 : a < 1 := hab.trans (hbc.trans hc1)
  have hcont : ContinuousOn (fun z => ‖F z‖) (closedBall (0 : ℂ) a) :=
    (hF.continuousOn.mono (closedBall_subset_ball ha1)).norm
  obtain ⟨w, hw, hmax⟩ := (isCompact_closedBall (0 : ℂ) a).exists_isMaxOn
    ⟨0, by simp [ha.le]⟩ hcont
  have hsup : diskSupNorm F a ≤ ‖F w‖ :=
    csSup_le (Nonempty.image _ ⟨w, hw⟩) (by rintro v ⟨z, hz, rfl⟩; exact hmax hz)
  exact hmain F t w hF hbound ht ht1 (by simpa using hw) (htmax.trans hsup)

end ModifiedCartan
