import ModifiedCartan.AbsorptionTheorem
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
set_option autoImplicit false
open Set Finset
namespace ModifiedCartan

/-- Dimension of the span of the actual restrictions to the specified domain. -/
def functionRank {m : ℕ} (a : Fin m → ℂ → ℂ) (U : Set ℂ) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (range (fun i => fun z : U => a i z)))

theorem functionRank_scaled_subfamily {m k : ℕ} (a : Fin m → ℂ → ℂ) (U : Set ℂ)
    (ι : Fin k → Fin m) (c : Fin k → ℂ) :
    functionRank (fun i z => c i * a (ι i) z) U ≤ functionRank a U := by
  let v := fun i => fun z : U => a i z
  let : FiniteDimensional ℂ (Submodule.span ℂ (range v)) :=
    FiniteDimensional.span_of_finite ℂ (finite_range v)
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Submodule.smul_mem _ (c i) (Submodule.subset_span (mem_range_self (ι i)))

/-- Rank deficiency supplies a relation with a fixed maximal nonzero coefficient. -/
theorem functionRank_relation {m : ℕ} {a : Fin m → ℂ → ℂ} {U : Set ℂ}
    (h : functionRank a U < m) :
    ∃ c : Fin m → ℂ, ∃ j : Fin m, c j ≠ 0 ∧ (∀ i, ‖c i‖ ≤ ‖c j‖) ∧
      ∀ z ∈ U, ∑ i, c i * a i z = 0 := by
  classical
  let v := fun i => fun z : U => a i z
  have hdep : ¬ LinearIndependent ℂ v := by
    intro hi
    have heq := finrank_span_eq_card hi
    have he : functionRank a U = m := by simpa [functionRank, v] using heq
    omega
  obtain ⟨c, hsum, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨j, _hj, hmax⟩ := univ.exists_max_image (fun i => ‖c i‖) ⟨k, mem_univ k⟩
  refine ⟨c, j, ?_, fun i => hmax i (mem_univ i), ?_⟩
  · intro hj0
    have hkn := hmax k (mem_univ k)
    rw [hj0, norm_zero] at hkn
    exact hk (norm_eq_zero.mp (le_antisymm hkn (norm_nonneg _)))
  · intro z hz
    have he := congrFun hsum ⟨z, hz⟩
    simpa [v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

end ModifiedCartan
