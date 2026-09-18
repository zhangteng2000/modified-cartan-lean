import ModifiedCartan.TorusMomentPolynomials

noncomputable section
set_option autoImplicit false
open Set Finset MvPolynomial
namespace ModifiedCartan

theorem torusJetCoordinates_injective {N : ℕ} :
    Function.Injective (fun w : (Fin N → ℂ) × (Fin N → ℂ) =>
      torusJetCoordinates w.1 w.2) := by
  intro a b h
  apply Prod.ext
  · funext j
    simpa [torusJetCoordinates] using congrFun h (0, j)
  · funext j
    simpa [torusJetCoordinates] using congrFun h (2, j)

theorem torus_null_zeroLocus_reconstruction {N : ℕ} (E : TorusEquations N)
    {w : Fin 3 × Fin N → ℂ} (hw : w ∈ MvPolynomial.zeroLocus ℂ E.nullIdeal) :
    ∃ x v : Fin N → ℂ, x ∈ E.locus ∧ kobayashiRoyden E.locus x v = 0 ∧
      torusJetCoordinates x v = w := by
  have hp : ∀ a, eval w (E.nullPolynomial a) = 0 := by
    rw [TorusEquations.nullIdeal, MvPolynomial.zeroLocus_span] at hw
    intro a
    exact hw _ (mem_range_self a)
  let x : Fin N → ℂ := fun j => w (0, j)
  let v : Fin N → ℂ := fun j => w (2, j)
  have hinv : ∀ j, x j * w (1, j) = 1 := by
    intro j
    have h := hp (Sum.inl j)
    simpa [TorusEquations.nullPolynomial, torusInversePolynomial, sub_eq_zero, x] using h
  have hx : ∀ j, x j ≠ 0 := by
    intro j hz
    have h := hinv j
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have hw1 : ∀ j, (x j)⁻¹ = w (1, j) := by
    intro j
    exact inv_eq_of_mul_eq_one_right (hinv j)
  have hcoord : torusJetCoordinates x v = w := by
    funext a
    rcases a with ⟨a, j⟩
    fin_cases a <;> simp [torusJetCoordinates, x, v, ← hw1]
  have hm : ∀ i (k : Fin (E.terms i)), ∑ j,
      (E.polynomial i).orbitCoefficient x j *
        ((E.polynomial i).orbitRate x v j) ^ (k : ℕ) = 0 := by
    intro i k
    have h := hp (Sum.inr ⟨i, k⟩)
    rw [← hcoord] at h
    simpa only [TorusEquations.nullPolynomial, eval_torusMomentPolynomial] using h
  have hbase : x ∈ E.locus := by
    refine ⟨hx, ?_⟩
    intro i
    have h := (laurent_orbit_zero_iff_finite_equations (E.polynomial i) x v).mpr (hm i) 0
    have h0 : exponentialOrbit x v 0 = x := by
      funext j
      simp [exponentialOrbit]
    rw [h0] at h
    exact h
  exact ⟨x, v, hbase, (torus_locus_metric_zero_iff_moments E hbase).mpr hm, hcoord⟩

/-- The entire affine zero locus, including its inverse-coordinate equations,
is exactly the embedded set of zero metric directions. -/
theorem torus_nullDirections_image_eq_zeroLocus {N : ℕ} (E : TorusEquations N) :
    (fun w : E.locus × (Fin N → ℂ) => torusJetCoordinates w.1.val w.2) ''
      E.nullDirections = MvPolynomial.zeroLocus ℂ E.nullIdeal := by
  ext w
  constructor
  · rintro ⟨⟨x, v⟩, hxv, rfl⟩
    exact (torus_metric_zero_iff_polynomial_zeroLocus E x.property).mp hxv
  · intro hw
    obtain ⟨x, v, hx, hk, hcoord⟩ := torus_null_zeroLocus_reconstruction E hw
    exact ⟨(⟨x, hx⟩, v), hk, hcoord⟩

end ModifiedCartan
