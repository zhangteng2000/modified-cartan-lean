import ModifiedCartan.GrowthExceptional
import ModifiedCartan.NegligibleDerivatives

noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory Asymptotics
namespace ModifiedCartan

theorem logarithmic_growth_bound_eventually_lt (B : ℝ) :
    ∀ᶠ x : ℝ in atTop, B*(Real.log x+1) < x := by
  have hl : (fun x : ℝ => B*(Real.log x+1)) =o[atTop] (fun x => x) := by
    simpa only [Pi.add_apply,id_eq] using!
      (Real.isLittleO_log_id_atTop.add (isLittleO_const_id_atTop (1 : ℝ))).const_mul_left B
  filter_upwards [hl.bound (by norm_num : (0 : ℝ) < 1/2),eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hb := (le_abs_self (B*(Real.log x+1))).trans
    (by simpa only [Real.norm_eq_abs,abs_of_pos hx0] using hx)
  linarith

/-- A logarithmic estimate on a positive-measure set of growth-controlled
radii forces an absolute bound at the inner radius. The set of good radii may
depend on the function, and it need not be measurable. -/
theorem growth_bound_from_large_radius_set {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ → ℝ) (a b : ℝ) (S : Set ℝ),
      a ≤ b → ContinuousOn M (Icc a b) → MonotoneOn M (Icc a b) → 0 < M a →
      S ⊆ Icc a b → ENNReal.ofReal δ ≤ volume S →
      (∀ r ∈ S, r+1/M r ≤ b → M (r+1/M r) ≤ 2*M r → M r ≤ B*(Real.log (M r)+1)) →
      M a ≤ C := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (logarithmic_growth_bound_eventually_lt B)
  let C := max A (max 1 (4/δ))
  have hC : 0 < C := (by norm_num : (0 : ℝ) < 1).trans_le
    ((le_max_left (1 : ℝ) (4/δ)).trans (le_max_right A _))
  refine ⟨C,hC,?_⟩
  intro M a b S hab hc hm ha hS hsize hbound
  by_contra hn
  have hlarge : C < M a := lt_of_not_ge hn
  have hgap : 3/M a < δ := by
    apply (div_lt_iff₀ ha).mpr
    have h4 : 4/δ < M a := (le_max_right (1 : ℝ) (4/δ)).trans
      (le_max_right A _) |>.trans_lt hlarge
    have hmul := (div_lt_iff₀ hδ).mp h4
    nlinarith
  have hsize' : ENNReal.ofReal (3/M a) < volume S :=
    (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hgap |>.trans_le hsize
  obtain ⟨r,hr,hstep,hgrowth⟩ := exists_growth_radius_in_large_set hab hc hm ha hS hsize'
  have hMar := hm ⟨le_rfl,hab⟩ (hS hr) (hS hr).1
  have hAr : A ≤ M r := (le_max_left A _).trans (hlarge.le.trans hMar)
  exact (not_lt_of_ge (hbound r hr hstep hgrowth)) (hA (M r) hAr)

end ModifiedCartan
