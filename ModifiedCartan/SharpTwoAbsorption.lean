import ModifiedCartan.SharpTwoCoordinates
import ModifiedCartan.SharpTwoSubsequence
import ModifiedCartan.SharpTwoRectangleDecay
import ModifiedCartan.SharpTwoEndgame

noncomputable section
set_option autoImplicit false
open Filter Topology Complex Metric Set
namespace ModifiedCartan

/-- Sharp two-term absorption on an arbitrary open subset of the unit disk,
including disconnected sets and the diameter endpoint log 3. -/
theorem sharp_two_absorption {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩ1 : Ω ⊆ disk 1)
    (hdiam : HasHyperbolicDiameterLE Ω (Real.log 3)) : AbsorptionAt 2 Ω := by
  classical
  intro A a s hA ha hsmall hsum hsne
  by_contra hn
  have hno : ∀ i, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence
      (fun n z => (A i (φ n) z)⁻¹) 0 Ω := fun i hi => hn ⟨i, hi⟩
  obtain ⟨D⟩ := sharp_two_setup hΩ hΩ1 hdiam hA ha hsmall hsum hsne hno
  obtain ⟨t, ξ, hcoordinates⟩ := sharp_two_coordinates D
  obtain ⟨φ, hφ, x, y, R, T, X, hx, hy, hR, hT, hX, hxlim, hylim, hRlim, hTlim, hXlim⟩ :=
    sharp_two_parameter_subsequence D (fun n => ⟨(hcoordinates n).1, (hcoordinates n).2.1⟩)
      (fun n => (hcoordinates n).2.2.1)
  let D' := sharpTwoSetupSubsequence D hφ
  let g := fun n => scaledDiskSegment (D.ρ (φ n)) (D.point 0 (φ n)) (ξ (φ n)) (t (φ n))
  let G := scaledDiskSegment R x X T
  have hα : 0 < D.α := D.r_pos.trans D.r_lt
  have hR0 : 0 < R := hα.trans_le hR.1
  have hρ0 : ∀ n, 0 < D.ρ n := fun n => hα.trans_le (D.radius n).1
  have hβ1 : D.β < 1 := D.β_lt.trans D.v_lt
  have hq1 : D.q < 1 := D.q_lt.trans sharpRadius_lt_one
  have hT1 : |T| < 1 := by rw [abs_of_nonneg hT.1]; exact hT.2.trans_lt hq1
  have hRClim : Tendsto (fun n => (D.ρ (φ n) : ℂ)) atTop (𝓝 (R : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hRlim
  have hcenterlim : ‖x / (R : ℂ)‖ ≤ D.r / D.α := by
    apply le_of_tendsto ((hxlim.div hRClim (Complex.ofReal_ne_zero.mpr hR0.ne')).norm)
    exact Eventually.of_forall (fun n => (hcoordinates (φ n)).2.2.2.1)
  have hcenter1 : ‖x / (R : ℂ)‖ < 1 := hcenterlim.trans_lt ((div_lt_one hα).mpr D.r_lt)
  have hglim : CompactConvergence g G (disk 1) :=
    scaledDiskSegment_compactConvergence hRlim hxlim hXlim hTlim hR0.ne' hcenter1 hX hT1
  have hg : ∀ n, DifferentiableOn ℂ (g n) (disk 1) := fun n =>
    (hcoordinates (φ n)).2.2.2.2.1.differentiableOn
  have hgmap : ∀ n, MapsTo (g n) (disk 1) (closedBall 0 D.β) := by
    intro n z hz
    exact (closedBall_subset_closedBall (D.radius (φ n)).2.le)
      (ball_subset_closedBall ((hcoordinates (φ n)).2.2.2.2.2.1 hz))
  have hleftn : ∀ n, g n ((-t (φ n) : ℝ) : ℂ) = D.point 0 (φ n) :=
    fun n => (hcoordinates (φ n)).2.2.2.2.2.2.1
  have hrightn : ∀ n, g n (t (φ n) : ℂ) = D.point 1 (φ n) :=
    fun n => (hcoordinates (φ n)).2.2.2.2.2.2.2
  have hGleft : G ((-T : ℝ) : ℂ) = x := by
    dsimp [G, scaledDiskSegment]
    rw [diskSegmentMap_left, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hR0.ne')]
  have hGright : G (T : ℂ) = y := by
    have hp : Tendsto (fun n => (D.ρ (φ n), D.point 0 (φ n), ξ (φ n), t (φ n)))
        atTop (𝓝 (R, x, X, T)) := by
      simpa only [nhds_prod_eq] using hRlim.prodMk (hxlim.prodMk (hXlim.prodMk hTlim))
    have htC : Tendsto (fun n => (t (φ n) : ℂ)) atTop (𝓝 (T : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hTlim
    have hpz : Tendsto (fun n => ((D.ρ (φ n), D.point 0 (φ n), ξ (φ n), t (φ n)), (t (φ n) : ℂ)))
        atTop (𝓝 ((R, x, X, T), (T : ℂ))) := by
      simpa only [nhds_prod_eq] using hp.prodMk htC
    have htunit : (T : ℂ) ∈ disk 1 := by simpa [disk] using hT1
    have hlimit : Tendsto (fun n => g n (t (φ n) : ℂ)) atTop (𝓝 (G (T : ℂ))) :=
      (scaledDiskSegment_joint_continuousAt hR0.ne' hcenter1 hX hT1 htunit).tendsto.comp hpz
    have hlimit' : Tendsto (fun n => g n (t (φ n) : ℂ)) atTop (𝓝 y) := by
      simpa only [hrightn] using hylim
    exact tendsto_nhds_unique hlimit hlimit'
  have hsum' := compactConvergence_subsequence hsum hφ
  obtain ⟨h, hh, hrect1, hdecay⟩ := sharp_two_rectangle_decay D'
    (fun i n => hA i (φ n)) (fun i n => ha i (φ n)) hsum'
    (fun n => ⟨(hcoordinates (φ n)).1, (hcoordinates (φ n)).2.1⟩)
    (fun n => (hcoordinates (φ n)).2.2.1) hT.1 hT.2 hTlim hrightn
  have hW : CompactConvergence (fun n z => wronskian (fun i => a i (φ n)) (g n z)) 0
      (segmentRectangle T h) := fun K hK _ => hdecay.mono hK
  have hzero : Tendsto (fun n => a 0 (φ n) (g n ((-t (φ n) : ℝ) : ℂ)) /
      (∑ i, a i (φ n) (g n ((-t (φ n) : ℝ) : ℂ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hleftn] using D.endpoint_zero.comp hφ.tendsto_atTop
  have hone : Tendsto (fun n => a 0 (φ n) (g n (t (φ n) : ℂ)) /
      (∑ i, a i (φ n) (g n (t (φ n) : ℂ)))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, hrightn] using D.endpoint_one.comp hφ.tendsto_atTop
  exact sharp_two_fixed_domain_contradiction (fun i n => ha i (φ n)) hsum' hg hgmap hβ1 hglim
    hT.1 hh hrect1 hTlim (by rw [hGleft]; exact D.nonzero x hx)
    (by rw [hGright]; exact D.nonzero y hy) hW hzero hone

theorem sharpTwoAbsorption_proved : SharpTwoAbsorption :=
  fun _ _ hΩ hΩ1 hdiam => sharp_two_absorption hΩ hΩ1 hdiam

end ModifiedCartan
