import ModifiedCartan.LogPoisson

noncomputable section
set_option autoImplicit false
open Filter Topology Set Function Metric MeromorphicOn
namespace ModifiedCartan

/-- Remove any finitely supported effective divisor bounded by the actual zero orders.
The quotient is constructed by meromorphic normalization, including the zero locations. -/
theorem analytic_remove_finite_zeros {F : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (D : ℂ → ℤ) (hD : D.HasFiniteSupport)
    (hDpos : ∀ z, 0 ≤ D z)
    (horder : ∀ z ∈ U, (D z : WithTop ℤ) ≤ meromorphicOrderAt F z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, F z = (∏ᶠ a, (z - a) ^ D a) * g z) ∧
      (∀ z ∈ U, meromorphicOrderAt g z = meromorphicOrderAt F z - (D z : WithTop ℤ)) := by
  classical
  let P : ℂ → ℂ := ∏ᶠ a, (· - a) ^ D a
  have hP : ∀ z, AnalyticAt ℂ P z := fun z => FactorizedRational.analyticAt (hDpos z)
  have hPo : ∀ z, meromorphicOrderAt P z = (D z : WithTop ℤ) :=
    fun _ => FactorizedRational.meromorphicOrderAt_eq D hD
  let g := toMeromorphicNFOn (F / P) U
  have hFP : MeromorphicOn (F / P) U := hF.meromorphicOn.div (fun z _ => (hP z).meromorphicAt)
  have hgNF : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn _ _
  have hgo : ∀ z ∈ U, meromorphicOrderAt g z = meromorphicOrderAt F z - (D z : WithTop ℤ) := by
    intro z hz
    rw [meromorphicOrderAt_toMeromorphicNFOn hFP hz,
      meromorphicOrderAt_div (hF z hz).meromorphicAt (hP z).meromorphicAt, hPo]
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    apply (hgNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [hgo z hz]
    by_cases ht : meromorphicOrderAt F z = ⊤
    · simp [ht]
    · have hle := horder z hz
      lift meromorphicOrderAt F z to ℤ using ht with n hn
      exact_mod_cast (sub_nonneg.mpr (show D z ≤ n by exact_mod_cast hle))
  refine ⟨g, hg, ?_, hgo⟩
  intro z hz
  have hPn : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 := by
    rcases (hP z).meromorphicAt.eventually_eq_zero_or_eventually_ne_zero with he | hn
    · have ht : meromorphicOrderAt P z = ⊤ := meromorphicOrderAt_eq_top_iff.mpr he
      rw [hPo] at ht
      exact False.elim (WithTop.coe_ne_top ht)
    · exact hn
  have heq : F =ᶠ[𝓝[≠] z] (fun w => P w * g w) := by
    filter_upwards [hFP.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hPn] with w hw hPw
    change g w = F w / P w at hw
    rw [hw, mul_div_cancel₀ _ hPw]
  have hvalue : F z = P z * g z :=
    tendsto_nhds_unique ((hF z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((((hP z).continuousAt.mul (hg z hz).continuousAt).tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  simpa [P, FactorizedRational.finprod_eq_fun hD] using hvalue

/-- Remove all zeros in a closed smaller disk while retaining analyticity throughout
the unit disk. Zeros on the smaller boundary are included with their multiplicities. -/
theorem finite_zero_factorization {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (disk 1)) {w : ℂ} (hw : w ∈ disk 1) (hFw : F w ≠ 0)
    {T : ℝ} (_hT : 0 ≤ T) (hT1 : T < 1) :
    ∃ (s : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ a ∈ s, ‖a‖ ≤ T ∧ 0 < m a) ∧
      AnalyticOnNhd ℂ g (disk 1) ∧
      (∀ z ∈ closedBall (0 : ℂ) T, g z ≠ 0) ∧
      (∀ z ∈ disk 1, F z = (∏ a ∈ s, (z - a) ^ m a) * g z) := by
  classical
  have hA := hF.analyticOnNhd Metric.isOpen_ball
  have hsub : closedBall (0 : ℂ) T ⊆ disk 1 := closedBall_subset_ball hT1
  have hAT := hA.mono hsub
  let D := MeromorphicOn.divisor F (closedBall (0 : ℂ) T)
  have hD : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hDpos : ∀ z, 0 ≤ D z := hAT.divisor_nonneg
  have hfinite : ∀ z ∈ disk 1, meromorphicOrderAt F z ≠ ⊤ := by
    intro z hz
    apply hA.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_ball (0 : ℂ) 1).isPreconnected hw hz
    rw [(hA w hw).meromorphicOrderAt_eq, (hA w hw).analyticOrderAt_eq_zero.mpr hFw]
    simp
  have hDeq : ∀ z ∈ closedBall (0 : ℂ) T, (D z : WithTop ℤ) = meromorphicOrderAt F z := by
    intro z hz
    dsimp [D]
    rw [hAT.meromorphicOn.divisor_apply hz]
    exact WithTop.coe_untop₀_of_ne_top (hfinite z (hsub hz))
  have horder : ∀ z ∈ disk 1, (D z : WithTop ℤ) ≤ meromorphicOrderAt F z := by
    intro z hz
    by_cases hzT : z ∈ closedBall (0 : ℂ) T
    · exact (hDeq z hzT).le
    · have hDz : D z = 0 := D.apply_eq_zero_of_notMem hzT
      rw [hDz]
      exact (hA z hz).meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr (hA z hz)
  obtain ⟨g, hg, hfg, hgo⟩ := analytic_remove_finite_zeros hA D hD hDpos horder
  let s := hD.toFinset
  let m : ℂ → ℕ := fun a => (D a).toNat
  refine ⟨s, m, g, ?_, hg, ?_, ?_⟩
  · intro a ha
    have hDa : D a ≠ 0 := by simpa [s, Function.mem_support] using ha
    refine ⟨by simpa using D.supportWithinDomain hDa, ?_⟩
    have := hDpos a
    dsimp [m]
    omega
  · intro z hz
    apply (hg z (hsub hz)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
    rw [hgo z (hsub hz), ← hDeq z hz]
    simp
  · intro z hz
    rw [hfg z hz]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset (s := s)]
    · apply Finset.prod_congr rfl
      intro a _
      change (z - a) ^ D a = (z - a) ^ (D a).toNat
      simpa only [Int.toNat_of_nonneg (hDpos a)] using (zpow_natCast (z - a) (D a).toNat)
    · intro a ha
      by_contra hn
      have hDa : D a = 0 := by simpa [s, Function.mem_support] using hn
      exact ha (by simp [hDa])

end ModifiedCartan
