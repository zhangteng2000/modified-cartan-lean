import ModifiedCartan.ProximityLocal
import ModifiedCartan.CauchyBounds

noncomputable section
set_option autoImplicit false
open Filter Metric Set Real Topology
namespace ModifiedCartan

/-- Leibniz's rule expresses the next derivative quotient using lower quotients
and derivatives of the logarithmic derivative. -/
theorem derivative_quotient_recurrence {F : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hnz : F z ≠ 0) (n : ℕ) :
    iteratedDeriv (n + 1) F z / F z =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i (logDeriv F) z *
        (iteratedDeriv (n - i) F z / F z) := by
  have he : deriv F =ᶠ[𝓝 z] (fun w => logDeriv F w * F w) := by
    filter_upwards [hF.continuousAt.eventually_ne hnz] with w hw
    simp [logDeriv, hw]
  have hlog : AnalyticAt ℂ (logDeriv F) z := by
    simpa only [logDeriv, Pi.div_def] using hF.deriv.div hF hnz
  rw [iteratedDeriv_succ', (he.iteratedDeriv n).eq_of_nhds,
    iteratedDeriv_fun_mul hlog.contDiffAt hF.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem holomorphic_nonzero_codiscrete_circle {F : ℂ → ℂ} {R : ℝ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hR0 : 0 ≤ R) (hR1 : R < 1)
    {w : ℂ} (hw : w ∈ disk 1) (hFw : F w ≠ 0) :
    ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |R|), F z ≠ 0 := by
  have hA := hF.analyticOnNhd isOpen_ball
  have hconn : IsConnected (disk (1 : ℝ)) :=
    ⟨⟨0, by simp [disk]⟩, (convex_ball (0 : ℂ) 1).isPreconnected⟩
  have hne := hA.preimage_zero_mem_codiscreteWithin hFw hw hconn
  have hsub : sphere (0 : ℂ) |R| ⊆ disk 1 := by
    rw [abs_of_nonneg hR0]
    exact sphere_subset_closedBall.trans (closedBall_subset_ball hR1)
  exact (codiscreteWithin_mono hsub) hne

theorem derivative_quotient_proximity_recurrence {F : ℂ → ℂ} {R : ℝ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hR0 : 0 < R) (hR1 : R < 1)
    {w : ℂ} (hw : w ∈ disk 1) (hFw : F w ≠ 0) (n : ℕ) :
    proximityMean (fun z => iteratedDeriv (n + 1) F z / F z) R ≤
      (∑ i ∈ Finset.range (n + 1),
        (Real.posLog (n.choose i : ℝ) + proximityMean (iteratedDeriv i (logDeriv F)) R +
          proximityMean (fun z => iteratedDeriv (n - i) F z / F z) R)) + Real.log (n + 1) := by
  let U := sphere (0 : ℂ) |R|
  have hsub : U ⊆ disk 1 := by
    dsimp [U]
    rw [abs_of_pos hR0]
    exact sphere_subset_closedBall.trans (closedBall_subset_ball hR1)
  have hA := hF.analyticOnNhd isOpen_ball
  have hAM := (hA.mono hsub).meromorphicOn
  have hL : ∀ i, MeromorphicOn (iteratedDeriv i (logDeriv F)) U :=
    fun i => meromorphicOn_iteratedDeriv (fun z hz => (hAM z hz).logDeriv) i
  have hQ : ∀ i, MeromorphicOn (fun z => iteratedDeriv i F z / F z) U :=
    fun i => (meromorphicOn_iteratedDeriv hAM i).div hAM
  let f : ℕ → ℂ → ℂ := fun i z => (n.choose i : ℂ) * iteratedDeriv i (logDeriv F) z *
    (iteratedDeriv (n - i) F z / F z)
  have hf : ∀ i, MeromorphicOn (f i) U := fun i =>
    ((show MeromorphicOn (fun _ : ℂ => (n.choose i : ℂ)) U from
      fun _ _ => analyticAt_const.meromorphicAt).mul (hL i)).mul (hQ (n - i))
  have hsum : MeromorphicOn (fun z => ∑ i ∈ Finset.range (n + 1), f i z) U :=
    fun z hz => MeromorphicAt.fun_sum (fun i _ => hf i z hz)
  have he : (fun z => iteratedDeriv (n + 1) F z / F z) =ᶠ[codiscreteWithin U]
      (fun z => ∑ i ∈ Finset.range (n + 1), f i z) := by
    filter_upwards [holomorphic_nonzero_codiscrete_circle hF hR0.le hR1 hw hFw,
      self_mem_codiscreteWithin U] with z hnz hz
    exact derivative_quotient_recurrence (hA z (hsub hz)) hnz n
  rw [proximityMean_congr_codiscrete hR0.ne' (hQ (n + 1)) hsum he]
  apply (proximityMean_sum_le _ f (fun i _ => hf i)).trans
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one]
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro i _
  have hmul := proximityMean_mul_le
    ((show MeromorphicOn (fun _ : ℂ => (n.choose i : ℂ)) U from
      fun _ _ => analyticAt_const.meromorphicAt).mul (hL i)) (hQ (n - i))
  apply hmul.trans
  have hc := proximityMean_const_mul_le (n.choose i : ℂ) (hL i)
  simpa only [Complex.norm_natCast, Pi.mul_def] using add_le_add hc (le_refl (proximityMean
    (fun z => iteratedDeriv (n - i) F z / F z) R))

end ModifiedCartan
