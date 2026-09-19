import ModifiedCartan.CartanCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory intervalIntegral
namespace ModifiedCartan

theorem radialLog_nonneg {u r : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ radialLog u r := by
  have hlog' : Real.log (r-u) ≤ 0 := by
    rw [← Real.log_abs]
    exact Real.log_nonpos (abs_nonneg _) (abs_le.mpr ⟨by linarith,by linarith⟩)
  exact sub_nonneg.mpr (hlog'.trans (Real.log_nonneg (by norm_num)))

/-- A quantitative lower bound on almost every concentric circle, with an
integrable loss whose total is controlled by one nonzero interior value. -/
theorem cartan_integrable_radial_loss {a b c T R : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hbc : b < c)
    (haT : a < T) (hcT : c < T) (hTR : T < R) (hR1 : R < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℂ → ℂ) (t : ℝ) (w : ℂ),
      DifferentiableOn ℂ F (disk 1) → (∀ z ∈ disk 1, ‖F z‖ ≤ 1) →
      0 < t → t ≤ 1 → ‖w‖ ≤ a → t ≤ ‖F w‖ →
      ∃ E : ℝ → ℝ, IntervalIntegrable E volume b c ∧
        (∀ ρ ∈ Icc b c, 0 ≤ E ρ) ∧
        (∫ ρ in b..c, E ρ) ≤ K * (-Real.log t) ∧
        ∀ᵐ ρ ∂volume.restrict (Icc b c),
          ∀ z : ℂ, ‖z‖ = ρ → F z ≠ 0 ∧ -Real.log ‖F z‖ ≤ E ρ := by
  have haR : a < R := haT.trans hTR
  have hc : 0 < c := hb.trans_lt hbc
  have hT : 0 < T := ha.trans haT
  have hR : 0 < R := hT.trans hTR
  obtain ⟨q₀,hq₀,hq₀1,hqbound⟩ := blaschkeFactor_uniform_bound hT.le ha.le hTR haR
  let q := (q₀+1)/2
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hq₀q : q₀ ≤ q := by dsimp [q]; linarith
  let L := -Real.log q
  have hL : 0 < L := neg_pos.mpr (Real.log_neg hq hq1)
  let H := harnackPower T a c
  have hH : 0 < H := harnackPower_pos ha.le hc.le haT hcT
  let K := (c-b)*H + (Real.log 2 + 3)/L
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : 0 < K := add_pos (mul_pos (sub_pos.mpr hbc) hH)
    (div_pos (by linarith) hL)
  refine ⟨K,hK,?_⟩
  intro F t w hF hbound ht ht1 hw htF
  have hwR : w ∈ closedBall (0 : ℂ) R := by simpa using hw.trans haR.le
  have hRsub : closedBall (0 : ℂ) R ⊆ disk 1 := closedBall_subset_ball hR1
  have hFw : F w ≠ 0 := norm_pos_iff.mp (ht.trans_le htF)
  obtain ⟨s,m,Q,hs,hQ,hQnz,hQbound,hfact⟩ :=
    bounded_blaschke_factorization hF hbound (hRsub hwR) hFw hT.le hTR hR1
  let N : ℕ := ∑ v ∈ s, m v
  have hprodq : ‖∏ v ∈ s, blaschkeFactor R v w ^ m v‖ ≤ q^N := by
    simp only [norm_prod,norm_pow]
    dsimp [N]
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _)
    intro v hv
    exact pow_le_pow_left₀ (norm_nonneg _) ((hqbound v w (hs v hv).1 hw).trans hq₀q) _
  have hprod1 : ‖∏ v ∈ s, blaschkeFactor R v w ^ m v‖ ≤ 1 :=
    hprodq.trans (pow_le_one₀ hq.le hq1.le)
  have htq : t ≤ q^N := by
    apply htF.trans
    rw [hfact w hwR,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hQbound w hwR)).trans hprodq
  have htQ : t ≤ ‖Q w‖ := by
    apply htF.trans
    rw [hfact w hwR,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hprod1
  have hN : (N : ℝ) ≤ (-Real.log t)/L := power_bound_zero_count ht hq hq1 htq
  let E : ℝ → ℝ := fun ρ => H * (-Real.log t) + ∑ v ∈ s, (m v : ℝ) * radialLog ‖v‖ ρ
  have hi : IntervalIntegrable E volume b c := by
    have hsum := IntervalIntegrable.sum s (fun v _ => (radialLog_integrable ‖v‖ b c).const_mul (m v : ℝ))
    convert! (show IntervalIntegrable (fun _ : ℝ => H * (-Real.log t)) volume b c from intervalIntegrable_const).add hsum using 1
    ext ρ
    simp [E]
  have hepos : ∀ ρ ∈ Icc b c, 0 ≤ E ρ := by
    intro ρ hρ
    apply add_nonneg (mul_nonneg hH.le (neg_nonneg.mpr (Real.log_nonpos ht.le ht1)))
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg (Nat.cast_nonneg _) (radialLog_nonneg (norm_nonneg _) ((hs v hv).1.trans (hTR.le.trans hR1.le))
      (hb.trans hρ.1) (hρ.2.trans (hcT.le.trans (hTR.le.trans hR1.le))))
  have heint : (∫ ρ in b..c, E ρ) ≤ K * (-Real.log t) := by
    have hexpr : E = (fun _ => H * (-Real.log t)) + ∑ v ∈ s, fun ρ => (m v : ℝ) * radialLog ‖v‖ ρ := by
      ext ρ
      simp [E]
    rw [hexpr]
    simp only [Pi.add_apply]
    rw [intervalIntegral.integral_add (show IntervalIntegrable (fun _ : ℝ => H * (-Real.log t)) volume b c from intervalIntegrable_const)
      (IntervalIntegrable.sum s (fun v _ => (radialLog_integrable ‖v‖ b c).const_mul (m v : ℝ)))]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum (fun v _ => (radialLog_integrable ‖v‖ b c).const_mul (m v : ℝ)),
      intervalIntegral.integral_const]
    simp only [intervalIntegral.integral_const_mul,smul_eq_mul]
    have hsum : (∑ v ∈ s, (m v : ℝ) * ∫ ρ in b..c, radialLog ‖v‖ ρ) ≤
        (N : ℝ) * (Real.log 2 + 3) := by
      dsimp [N]
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left
        (radialLog_integral_bound hb hbc (hcT.le.trans (hTR.le.trans hR1.le))
          (norm_nonneg _) ((hs v hv).1.trans (hTR.le.trans hR1.le))) (Nat.cast_nonneg _))
    have hmult := mul_le_mul_of_nonneg_right hN (by linarith : 0 ≤ Real.log 2 + 3)
    apply (add_le_add (le_refl _) (hsum.trans hmult)).trans_eq
    dsimp [K]
    ring
  refine ⟨E,hi,hepos,heint,?_⟩
  have hae : ∀ᵐ ρ : ℝ, ∀ v : s, ρ ≠ ‖(v : ℂ)‖ :=
    ae_all_iff.mpr (fun v => volume.ae_ne ‖(v : ℂ)‖)
  filter_upwards [ae_restrict_of_ae hae,self_mem_ae_restrict measurableSet_Icc] with ρ hρne hρ
  intro z hz
  have hzT : z ∈ closedBall (0 : ℂ) T := by simpa [hz] using hρ.2.trans hcT.le
  have hzR := closedBall_subset_closedBall hTR.le hzT
  have hBl : ∀ v ∈ s, 0 < ‖blaschkeFactor R v z‖ ∧
      -radialLog ‖v‖ ρ ≤ Real.log ‖blaschkeFactor R v z‖ := by
    intro v hv
    exact blaschkeFactor_log_lower hR hR1.le ((hs v hv).1.trans_lt hTR) hz
      (hρ.2.trans (hcT.le.trans hTR.le)) (hρne ⟨v,hv⟩)
  have hQlog : H * Real.log t ≤ Real.log ‖Q z‖ :=
    zero_free_log_lower ha.le hc.le haT hcT
      (hQ.mono (closedBall_subset_ball (hTR.trans hR1))) hQnz
      (fun v hv => hQbound v (closedBall_subset_closedBall hTR.le hv))
      hw (hz.trans_le hρ.2) ht htQ
  have hBnz : ∀ v ∈ s, ‖blaschkeFactor R v z‖^m v ≠ 0 :=
    fun v hv => pow_ne_zero _ (hBl v hv).1.ne'
  have hQnorm : 0 < ‖Q z‖ := norm_pos_iff.mpr (hQnz z hzT)
  have hFnorm : 0 < ‖F z‖ := by
    rw [hfact z hzR,norm_mul,norm_prod]
    simp only [norm_pow]
    exact mul_pos (Finset.prod_pos (fun v hv => pow_pos (hBl v hv).1 _)) hQnorm
  refine ⟨norm_pos_iff.mp hFnorm,?_⟩
  have hlogF : Real.log ‖F z‖ =
      (∑ v ∈ s, (m v : ℝ) * Real.log ‖blaschkeFactor R v z‖) + Real.log ‖Q z‖ := by
    rw [hfact z hzR,norm_mul,norm_prod]
    simp only [norm_pow]
    rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr hBnz) hQnorm.ne',Real.log_prod hBnz]
    simp only [Real.log_pow]
  have hsum := Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hBl v hv).2 (Nat.cast_nonneg (m v)))
  simp only [mul_neg,Finset.sum_neg_distrib] at hsum
  rw [hlogF]
  dsimp [E]
  linarith

end ModifiedCartan
