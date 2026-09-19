import ModifiedCartan.RadialProximityExceptional

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

theorem exists_avoiding_finite_exceptional {ι : Type*} [Fintype ι]
    (S : Set ℝ) (E : ι → Set ℝ) (hsize : (∑ i, volume (E i)) < volume S) :
    ∃ r ∈ S, ∀ i, r ∉ E i := by
  have hnot : ¬ S ⊆ ⋃ i, E i := by
    intro hs
    exact (not_le_of_gt hsize) ((measure_mono hs).trans (measure_iUnion_fintype_le volume E))
  obtain ⟨r,hr,he⟩ := not_subset.mp hnot
  exact ⟨r,hr,fun i hi => he (mem_iUnion.mpr ⟨i,hi⟩)⟩

/-- The algebraic anchor step used for third- and fourth-order derived
fractions: lower denominator bounds and an upper numerator-factor bound
force a quantitative nonzero value of the remaining factor. -/
theorem log_anchor_of_product_ratio {m : ℕ} (F : Fin m → ℂ) {G H : ℂ}
    (L : Fin m → ℝ) {A : ℝ} (hF : ∀ i, F i ≠ 0)
    (hL : ∀ i, -L i ≤ Real.log ‖F i‖) (hG : ‖G‖ ≤ Real.exp A)
    (hratio : 1 < ‖G*H/(∏ i, F i)‖) :
    H ≠ 0 ∧ -(A+∑ i, L i) ≤ Real.log ‖H‖ := by
  have hnH : H ≠ 0 := by
    intro hh
    norm_num [hh] at hratio
  have hprod : 0 < ∏ i, ‖F i‖ := Finset.prod_pos (fun i _ => norm_pos_iff.mpr (hF i))
  rw [norm_div,norm_mul,norm_prod] at hratio
  have hmul : (∏ i, ‖F i‖) ≤ Real.exp A*‖H‖ := by
    have hh := (lt_div_iff₀ hprod).mp hratio
    simp only [one_mul] at hh
    exact hh.le.trans (mul_le_mul_of_nonneg_right hG (norm_nonneg H))
  have hlog := Real.log_le_log hprod hmul
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hnH),Real.log_exp,
    Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (hF i))] at hlog
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hL i)
  simp only [Finset.sum_neg_distrib] at hsum
  exact ⟨hnH,by linarith⟩

/-- Large derived fractions on a sufficiently large set of radii yield an
actual anchor after avoiding every denominator's radial exceptional set.
No measurability assumption on the projected radius set is required. -/
theorem radial_product_anchor {m : ℕ} (F : Fin m → ℂ → ℂ) (G H : ℂ → ℂ)
    (L : Fin m → ℝ) {b c A : ℝ} (S : Set ℝ) (hS : S ⊆ Icc b c)
    (hsize : (∑ i, volume (radialSmallValueSet (F i) b c (L i))) < volume S)
    (hG : ∀ r ∈ Icc b c, ∀ z : ℂ, ‖z‖ = r → ‖G z‖ ≤ Real.exp A)
    (hratio : ∀ r ∈ S, ∃ z : ℂ, ‖z‖ = r ∧ 1 < ‖G z*H z/(∏ i, F i z)‖) :
    ∃ w : ℂ, ‖w‖ ≤ c ∧ H w ≠ 0 ∧ -(A+∑ i, L i) ≤ Real.log ‖H w‖ := by
  obtain ⟨r,hr,hgood⟩ := exists_avoiding_finite_exceptional S
    (fun i => radialSmallValueSet (F i) b c (L i)) hsize
  obtain ⟨z,hz,hh⟩ := hratio r hr
  have hFnz : ∀ i, F i z ≠ 0 := fun i hn => hgood i ⟨hS hr,z,hz,Or.inl hn⟩
  have hFlo : ∀ i, -L i ≤ Real.log ‖F i z‖ := by
    intro i
    have hh : ¬ L i < -Real.log ‖F i z‖ := fun ht => hgood i ⟨hS hr,z,hz,Or.inr ht⟩
    linarith
  exact ⟨z,hz.trans_le (hS hr).2,log_anchor_of_product_ratio (fun i => F i z) L hFnz hFlo
    (hG r (hS hr) z hz) hh⟩

end ModifiedCartan
