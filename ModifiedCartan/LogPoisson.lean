import ModifiedCartan.Harmonic
import ModifiedCartan.AnalyticStatements
import Mathlib.Analysis.Complex.JensenFormula

noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate
open Complex InnerProductSpace Metric Real Filter Topology MeromorphicOn
namespace ModifiedCartan

theorem blaschke_norm_identity (R : ℝ) (a z : ℂ) :
    ‖((R ^ 2 : ℝ) : ℂ) - conj a * z‖ ^ 2 - R ^ 2 * ‖z - a‖ ^ 2 =
      (R ^ 2 - ‖a‖ ^ 2) * (R ^ 2 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem blaschke_numerator_ne_zero {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) :
    ((R ^ 2 : ℝ) : ℂ) - conj a * z ≠ 0 := by
  intro hzero
  have heq := congrArg norm (sub_eq_zero.mp hzero)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_sq,
    norm_mul, Complex.norm_conj] at heq
  have hprod := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
  nlinarith

/-- The Poisson comparison for a logarithmic factor with its zero in the closed disk.
The boundary-zero case uses mathlib's integrable singularity theorem. -/
theorem log_factor_le_poisson {R : ℝ} (hR : 0 < R) {a w : ℂ}
    (ha : a ∈ closedBall (0 : ℂ) R) (hw : w ∈ ball (0 : ℂ) R) (hwa : w ≠ a) :
    Real.log ‖w - a‖ ≤
      circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) * (fun z => Real.log ‖z - a‖)) 0 R := by
  have haN : ‖a‖ ≤ R := by simpa using ha
  rcases haN.eq_or_lt with heq | haR
  · have hsphere : a ∈ sphere (0 : ℂ) R := by simpa [mem_sphere, dist_eq_norm] using heq
    rw [circleAverage_re_herglotzRieszKernel_mul_log hsphere hw]
  · let F : ℂ → ℂ := fun z => ((R ^ 2 : ℝ) : ℂ) - conj a * z
    have hF : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R) := by
      intro z _
      dsimp [F]
      fun_prop
    have hFnz : ∀ z ∈ closedBall (0 : ℂ) R, F z ≠ 0 := by
      intro z hz
      exact blaschke_numerator_ne_zero hR haR (by simpa using hz)
    have hlog : HarmonicOnNhd (fun z => Real.log ‖F z‖) (closedBall (0 : ℂ) R) :=
      fun z hz => (hF z hz).harmonicAt_log_norm (hFnz z hz)
    have hv : HarmonicOnNhd (fun z => Real.log ‖F z‖ - Real.log R) (closedBall (0 : ℂ) R) :=
      hlog.sub (harmonicOnNhd_const _)
    have hboundary : ∀ z ∈ sphere (0 : ℂ) |R|,
        Real.log ‖F z‖ - Real.log R = Real.log ‖z - a‖ := by
      intro z hz
      have hzN : ‖z‖ = R := by simpa [mem_sphere, dist_eq_norm, abs_of_pos hR] using hz
      have hn := blaschke_norm_identity R a z
      rw [hzN, sub_self, mul_zero] at hn
      have heq : ‖F z‖ = R * ‖z - a‖ := by
        dsimp [F]
        apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hR.le (norm_nonneg _))).mp
        nlinarith only [hn]
      have hza : z - a ≠ 0 := by
        intro he
        have := congrArg norm (sub_eq_zero.mp he)
        linarith
      rw [heq, Real.log_mul hR.ne' (norm_ne_zero_iff.mpr hza)]
      ring
    have hp : circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) *
        (fun z => Real.log ‖z - a‖)) 0 R = Real.log ‖F w‖ - Real.log R := by
      rw [← hv.circleAverage_re_herglotzRieszKernel_smul hw]
      apply circleAverage_congr_sphere
      intro z hz
      simp only [Pi.mul_apply, smul_eq_mul]
      rw [hboundary z hz]
    rw [hp]
    have hwN : ‖w‖ < R := by simpa using hw
    have hn := blaschke_norm_identity R a w
    have hprod : 0 ≤ (R ^ 2 - ‖a‖ ^ 2) * (R ^ 2 - ‖w‖ ^ 2) := by
      apply mul_nonneg <;> nlinarith [norm_nonneg a, norm_nonneg w]
    have hnorm : R * ‖w - a‖ ≤ ‖F w‖ := by
      dsimp [F]
      apply (sq_le_sq₀ (mul_nonneg hR.le (norm_nonneg _)) (norm_nonneg _)).mp
      nlinarith only [hn, hprod]
    have hwnz : ‖w - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwa)
    have hl := Real.log_le_log (mul_pos hR (lt_of_le_of_ne (norm_nonneg _) hwnz.symm)) hnorm
    rw [Real.log_mul hR.ne' hwnz] at hl
    linarith

/-- Poisson's inequality for the logarithm of an analytic function, allowing
zeros anywhere on the boundary circle. -/
theorem log_norm_le_poisson {F : ℂ → ℂ} {R : ℝ} {w : ℂ}
    (hF : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R))
    (hw : w ∈ ball (0 : ℂ) R) (hwne : F w ≠ 0) :
    Real.log ‖F w‖ ≤
      circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) * (fun z => Real.log ‖F z‖)) 0 R := by
  classical
  have hR : 0 < R := pos_of_mem_ball hw
  let D := MeromorphicOn.divisor F (closedBall (0 : ℂ) R)
  have hD : D.support.Finite := D.finiteSupport (isCompact_closedBall ..)
  let S := hD.toFinset
  have hfinite : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt F u ≠ ⊤ := by
    intro u
    apply hF.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected (ball_subset_closedBall hw) u.property
    rw [(hF w (ball_subset_closedBall hw)).meromorphicOrderAt_eq,
      (hF w (ball_subset_closedBall hw)).analyticOrderAt_eq_zero.mpr hwne]
    simp
  obtain ⟨g, hg, hgnz, heq⟩ := hF.meromorphicOn.extract_zeros_poles hfinite hD
  have hacc : AccPt w (𝓟 (closedBall (0 : ℂ) R)) := by
    apply accPt_iff_frequently_nhdsNE.mpr
    have hb : closedBall (0 : ℂ) R ∈ 𝓝 w :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hw) ball_subset_closedBall
    have hb' : ∀ᶠ z in 𝓝 w, z ∈ closedBall (0 : ℂ) R := hb
    exact (hb'.filter_mono nhdsWithin_le_nhds).frequently
  have hvalue := MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles hD
    (ball_subset_closedBall hw) hacc (hF w (ball_subset_closedBall hw)).meromorphicAt
    (hg w (ball_subset_closedBall hw)) (hgnz ⟨w, ball_subset_closedBall hw⟩) heq
  rw [(hF w (ball_subset_closedBall hw)).meromorphicTrailingCoeffAt_of_ne_zero hwne] at hvalue
  have hsvalue : (∑ᶠ a, (D a : ℝ) * Real.log ‖w - a‖) =
      ∑ a ∈ S, (D a : ℝ) * Real.log ‖w - a‖ := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    simp_all [S, Function.mem_support]
  rw [hsvalue] at hvalue
  have hlog := MeromorphicOn.extract_zeros_poles_log hgnz heq
  have hsum : (∑ᶠ a, (fun z => (D a : ℝ) * Real.log ‖z - a‖)) =
      ∑ a ∈ S, (fun z => (D a : ℝ) * Real.log ‖z - a‖) := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    by_contra hn
    have hz : D a = 0 := by simpa [S, Function.mem_support] using hn
    apply ha
    ext z
    simp [hz]
  change (fun z => Real.log ‖F z‖) =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)]
    (∑ᶠ a, (fun z => (D a : ℝ) * Real.log ‖z - a‖)) + (fun z => Real.log ‖g z‖) at hlog
  rw [hsum] at hlog
  let P := Complex.re ∘ herglotzRieszKernel 0 w
  have hPc : ContinuousOn P (sphere (0 : ℂ) |R|) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hli : ∀ a : ℂ, CircleIntegrable (P * (fun z => Real.log ‖z - a‖)) 0 R := by
    intro a
    exact ((analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm).continuousOn_smul hPc
  have hgi : CircleIntegrable (P * (fun z => Real.log ‖g z‖)) 0 R := by
    have hgs : MeromorphicOn g (sphere (0 : ℂ) |R|) := by
      simpa [abs_of_pos hR] using (hg.mono sphere_subset_closedBall).meromorphicOn
    exact hgs.circleIntegrable_log_norm.continuousOn_smul hPc
  have hsi : CircleIntegrable (∑ a ∈ S, (D a : ℝ) •
      (P * (fun z => Real.log ‖z - a‖))) 0 R := by
    apply CircleIntegrable.sum
    intro a _
    exact (hli a).const_smul
  have haverage : circleAverage (P * (fun z => Real.log ‖F z‖)) 0 R =
      (∑ a ∈ S, (D a : ℝ) * circleAverage (P * (fun z => Real.log ‖z - a‖)) 0 R) +
        Real.log ‖g w‖ := by
    calc
      _ = circleAverage ((∑ a ∈ S, (D a : ℝ) • (P * (fun z => Real.log ‖z - a‖))) +
          P * (fun z => Real.log ‖g z‖)) 0 R := by
        apply circleAverage_congr_codiscreteWithin _ hR.ne'
        have hsphere : sphere (0 : ℂ) |R| ⊆ closedBall (0 : ℂ) R := by
          simpa [abs_of_pos hR] using (sphere_subset_closedBall (x := (0 : ℂ)) (ε := R))
        filter_upwards [hlog.filter_mono (codiscreteWithin_mono hsphere)] with z hz
        simp only [Pi.mul_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hz ⊢
        rw [hz, mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by
        rw [circleAverage_add hsi hgi, circleAverage_sum (fun a _ => (hli a).const_smul)]
        simp only [circleAverage_smul, smul_eq_mul]
        congr 1
        exact (show HarmonicOnNhd (fun z => Real.log ‖g z‖) (closedBall (0 : ℂ) R) from
          fun z hz => (hg z hz).harmonicAt_log_norm (hgnz ⟨z, hz⟩)).circleAverage_re_herglotzRieszKernel_smul hw
  rw [haverage, hvalue]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro a haS
  have haD : D a ≠ 0 := by simpa [S, Function.mem_support] using haS
  have ha : a ∈ closedBall (0 : ℂ) R := D.supportWithinDomain haD
  have hwa : w ≠ a := by
    intro he
    subst a
    apply haD
    dsimp [D]
    rw [hF.divisor_apply (ball_subset_closedBall hw),
      (hF w (ball_subset_closedBall hw)).analyticOrderAt_eq_zero.mpr hwne]
    simp
  exact mul_le_mul_of_nonneg_left (log_factor_le_poisson hR ha hw hwa)
    (by exact_mod_cast hF.divisor_nonneg a)

/-- The manuscript's off-center logarithmic mean inequality with no restriction
on zeros on the integration circle. -/
theorem poisson_mean_inequality {F : ℂ → ℂ} {R : ℝ} {w : ℂ}
    (hF : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R))
    (hw : w ∈ ball (0 : ℂ) R) (hwne : F w ≠ 0) :
    let q := (R + ‖w‖) / (R - ‖w‖)
    q * Real.log ‖F w‖ - (q ^ 2 - 1) * proximityMean F R ≤
      circleAverage (fun z => Real.log ‖F z‖) 0 R := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hwR : ‖w‖ < R := by simpa using hw
  let q := (R + ‖w‖) / (R - ‖w‖)
  let h := (R - ‖w‖) / (R + ‖w‖)
  let P := Complex.re ∘ herglotzRieszKernel 0 w
  have hq : 0 < q := div_pos (by positivity) (by linarith)
  have hqh : q * h = 1 := by
    dsimp [q, h]
    field_simp [ne_of_gt (sub_pos.mpr hwR), ne_of_gt (show 0 < R + ‖w‖ by positivity)]
  have hFs : MeromorphicOn F (sphere (0 : ℂ) |R|) := by
    simpa [abs_of_pos hR] using (hF.mono sphere_subset_closedBall).meromorphicOn
  have hlogi := hFs.circleIntegrable_log_norm
  have hposi := hFs.circleIntegrable_posLog_norm
  have hPc : ContinuousOn P (sphere (0 : ℂ) |R|) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)
  have hmono := circleAverage_mono (hlogi.continuousOn_smul hPc)
    ((hlogi.const_smul (a := h)).add (hposi.const_smul (a := q - h))) (fun z hz => ?_)
  · rw [circleAverage_add (hlogi.const_smul (a := h)) (hposi.const_smul (a := q - h)),
      circleAverage_smul, circleAverage_smul] at hmono
    have hp := (log_norm_le_poisson hF hw hwne).trans hmono
    have hm := mul_le_mul_of_nonneg_left hp hq.le
    change q * Real.log ‖F w‖ - (q ^ 2 - 1) * proximityMean F R ≤ _
    rw [proximityMean, ValueDistribution.proximity_top]
    simp only [smul_eq_mul] at hm
    have hid (I J : ℝ) : q * (h * I + (q - h) * J) = I + (q ^ 2 - 1) * J := by
      calc
        _ = (q * h) * I + (q ^ 2 - q * h) * J := by ring
        _ = _ := by rw [hqh]; ring
    rw [hid] at hm
    linarith
  · have hz' : z ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hz
    have hlo : h ≤ P z := by
      simpa [h, P, Function.comp_apply, herglotzRieszKernel, sub_zero] using
        le_re_herglotzRieszKernel hz' hw
    have hhi : P z ≤ q := by
      simpa [q, P, Function.comp_apply, herglotzRieszKernel, sub_zero] using
        re_herglotzRieszKernel_le hz' hw
    change P z * Real.log ‖F z‖ ≤
      h * Real.log ‖F z‖ + (q - h) * Real.posLog ‖F z‖
    rw [Real.posLog_apply]
    by_cases hx : 0 ≤ Real.log ‖F z‖
    · rw [max_eq_right hx]
      nlinarith [mul_le_mul_of_nonneg_right hhi hx]
    · rw [max_eq_left (le_of_not_ge hx)]
      nlinarith [mul_le_mul_of_nonpos_right hlo (le_of_not_ge hx)]

/-- Complete proof term for `lem:poisson-mean` in its original normalization. -/
theorem poissonMeanEstimate_proved : PoissonMeanEstimate := by
  intro F R w hF hw hwne
  have hR : 0 < R := pos_of_mem_ball hw
  have hratio : (1 + ‖w‖ / R) / (1 - ‖w‖ / R) = (R + ‖w‖) / (R - ‖w‖) := by
    field_simp
  dsimp only
  rw [hratio]
  exact poisson_mean_inequality hF hw hwne

end ModifiedCartan
