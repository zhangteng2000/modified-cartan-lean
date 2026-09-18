import ModifiedCartan.HolomorphicCancellation

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem nonzero_surrounding_circle_in_open {s : ℂ → ℂ}
    (hs : DifferentiableOn ℂ s (disk 1)) (hsne : ∃ z ∈ disk 1, s z ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hU1 : U ⊆ disk 1) {w : ℂ} (hw : w ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall w ρ ⊆ U ∧ ∀ z ∈ sphere w ρ, s z ≠ 0 := by
  have ha := hs.analyticOnNhd isOpen_ball
  have hp : ∀ᶠ z in 𝓝[≠] w, s z ≠ 0 := by
    rcases (ha w (hU1 hw)).eventually_eq_zero_or_eventually_ne_zero with hz | hn
    · have hall := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball (0 : ℂ) 1).isPreconnected (hU1 hw) hz
      obtain ⟨z, hzU, hzn⟩ := hsne
      exact False.elim (hzn (hall hzU))
    · exact hn
  have hgood : ∀ᶠ z in 𝓝 w, z ∈ U ∧ (z ≠ w → s z ≠ 0) := by
    filter_upwards [hU.mem_nhds hw, eventually_nhdsWithin_iff.mp hp] with z hz hn
    exact ⟨hz, hn⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨r / 2, half_pos hr,
    (fun z hz => (hsub (closedBall_subset_ball (half_lt_self hr) hz)).1), ?_⟩
  intro z hz
  apply (hsub (sphere_subset_ball (half_lt_self hr) hz)).2
  intro he
  subst z
  have : (0 : ℝ) = r / 2 := by simpa using hz
  linarith

/-- Move every possible failure point to one fixed compact zero-free set by the
maximum principle for reciprocals. The ambient open set may be disconnected. -/
theorem compact_failure_points_avoid_zeros {s : ℂ → ℂ}
    (hs : DifferentiableOn ℂ s (disk 1)) (hsne : ∃ z ∈ disk 1, s z ≠ 0)
    {U K : Set ℂ} (hU : IsOpen U) (hU1 : U ⊆ disk 1) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ U ∧ (∀ z ∈ L, s z ≠ 0) ∧
      ∀ A : ℂ → ℂ, IsHolomorphicUnit A (disk 1) → ∀ z ∈ K,
        ∃ w ∈ L, Real.log ‖A w‖ ≤ Real.log ‖A z‖ := by
  classical
  choose ρ hρ hρU hρnz using fun z : K => nonzero_surrounding_circle_in_open hs hsne hU hU1 (hKU z.property)
  have hcover : K ⊆ ⋃ z : K, ball (z : ℂ) (ρ z) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hρ ⟨z, hz⟩)⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun z : K => ball (z : ℂ) (ρ z)) (fun _ => isOpen_ball) hcover
  let L := ⋃ z ∈ T, sphere (z : ℂ) (ρ z)
  have hL : IsCompact L := T.isCompact_biUnion (fun z _ => isCompact_sphere _ _)
  have hLU : L ⊆ U := by
    intro w hw
    obtain ⟨z, hzT, hwz⟩ := mem_iUnion₂.mp hw
    exact hρU z (sphere_subset_closedBall hwz)
  refine ⟨L, hL, hLU, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hzT, hwz⟩ := mem_iUnion₂.mp hw
    exact hρnz z w hwz
  · intro A hA z hz
    obtain ⟨x, hxT, hzx⟩ := mem_iUnion₂.mp (hT hz)
    have hinv := hA.1.inv hA.2
    have hdiff : DifferentiableOn ℂ (fun z => (A z)⁻¹) (closure (ball (x : ℂ) (ρ x))) := by
      rw [closure_ball _ (hρ x).ne']
      exact hinv.mono ((hρU x).trans hU1)
    obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
      (nonempty_ball.mpr (hρ x)) hdiff.diffContOnCl
    have hws : w ∈ sphere (x : ℂ) (ρ x) := by simpa [frontier_ball _ (hρ x).ne'] using hw
    have hwL : w ∈ L := mem_iUnion₂.mpr ⟨x, hxT, hws⟩
    have hznz := hA.2 z (hU1 (hKU hz))
    have hwnz := hA.2 w (hU1 (hLU hwL))
    have hinvle : ‖A z‖⁻¹ ≤ ‖A w‖⁻¹ := by
      simpa only [Function.comp_apply, norm_inv, mem_ofPred_eq] using hmax (subset_closure hzx)
    have hnorm : ‖A w‖ ≤ ‖A z‖ := (inv_le_inv₀ (norm_pos_iff.mpr hznz) (norm_pos_iff.mpr hwnz)).mp hinvle
    exact ⟨w, hwL, Real.log_le_log (norm_pos_iff.mpr hwnz) hnorm⟩

end ModifiedCartan
