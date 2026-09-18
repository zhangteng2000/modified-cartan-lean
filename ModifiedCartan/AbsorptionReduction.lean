import ModifiedCartan.AbsorptionLinearAlgebra

noncomputable section
set_option autoImplicit false
open Filter Metric Set
namespace ModifiedCartan

/-- Remove a fixed maximal coefficient when a normalized linear combination
tends to zero, then apply the lower-dimensional absorption statement. -/
theorem absorption_of_vanishing_combination {m : ℕ} {ρ η : ℝ}
    (habs : AbsorptionAt m (disk ρ)) (hη : 0 < η)
    (A a : Family (m + 1)) (s : ℂ → ℂ)
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk η))
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk η))
    (hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) (fun _ => 0) (disk η))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk η))
    (hsne : ∃ z ∈ disk η, s z ≠ 0)
    (c : ℕ → Fin (m + 1) → ℂ) (hc : ∀ n, coefficientNormSq (c n) = 1)
    (j : Fin (m + 1)) (hmax : ∀ n i, ‖c n i‖ ≤ ‖c n j‖)
    (hcomb : CompactConvergence (fun n z => ∑ i, c n i * a i n z) (fun _ => 0) (disk η)) :
    ∃ i : Fin (m + 1), i ≠ j ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => (A i (φ n) z)⁻¹) (fun _ => 0) (disk (η * ρ)) := by
  have hcj := fun n => maximal_unit_coefficient_inv_bound (hc n) (hmax n)
  let d : Fin m → ℕ → ℂ := fun i n => 1 - c n (j.succAbove i) / c n j
  have hd : ∀ i n, ‖d i n‖ ≤ 2 := by
    intro i n
    have hdiv : ‖c n (j.succAbove i) / c n j‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr (hcj n).1)).mpr (hmax n _)
    apply (norm_sub_le _ _).trans
    rw [norm_one]
    linarith
  let A' : Family m := fun i => A (j.succAbove i)
  let a' : Family m := fun i n z => d i n * a (j.succAbove i) n z
  have hA' : ∀ i n, IsHolomorphicUnit (A' i n) (disk η) := fun i n => hA _ n
  have ha' : ∀ i n, DifferentiableOn ℂ (a' i n) (disk η) :=
    fun i n => (ha (j.succAbove i) n).const_mul (d i n)
  have hsmall' : ∀ i, CompactConvergence (fun n z => a' i n z / A' i n z) (fun _ => 0) (disk η) := by
    intro i
    have hdb : LocallyBounded (fun n (_ : ℂ) => d i n) (disk η) :=
      fun K _ _ => ⟨2, fun n _ _ => hd i n⟩
    apply compactConvergence_congr (compactConvergence_zero_mul (hsmall (j.succAbove i)) hdb)
    intro n z _
    dsimp [A', a']
    ring
  have hinvb : LocallyBounded (fun n (_ : ℂ) => (c n j)⁻¹) (disk η) :=
    fun K _ _ => ⟨(m + 1 : ℕ), fun n _ _ => (hcj n).2⟩
  have hquot := compactConvergence_zero_mul hcomb hinvb
  have hsum' : CompactConvergence (fun n z => ∑ i, a' i n z) s (disk η) := by
    have hdiff := compactConvergence_sub hsum hquot
    apply compactConvergence_congr (by simpa only [sub_zero] using hdiff)
    intro n z _
    have he := remove_one_coefficient_identity (fun i => a i n z) (c n) j (hcj n).1
    simpa only [a', d, div_eq_mul_inv] using he.symm
  obtain ⟨i, φ, hφ, hconv⟩ := absorption_rescale habs hη A' a' s hA' ha' hsmall' hsum' hsne
  exact ⟨j.succAbove i, Fin.succAbove_ne j i, φ, hφ, hconv⟩

end ModifiedCartan
