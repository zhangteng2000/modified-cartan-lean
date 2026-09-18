import ModifiedCartan.CombinationNorm
import Mathlib.Topology.Order.Compact

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

theorem continuous_coefficientNormSq (m : ℕ) : Continuous (@coefficientNormSq m) := by
  unfold coefficientNormSq
  fun_prop

theorem coefficient_norm_le_one {m : ℕ} {c : Fin m → ℂ} (hc : coefficientNormSq c = 1) (j : Fin m) :
    ‖c j‖ ≤ 1 := by
  have hs : ‖c j‖ ^ 2 ≤ coefficientNormSq c :=
    Finset.single_le_sum (fun i _ => sq_nonneg ‖c i‖) (Finset.mem_univ j)
  rw [hc] at hs
  nlinarith [norm_nonneg (c j)]

theorem coefficient_sphere_isCompact (m : ℕ) :
    IsCompact {c : Fin m → ℂ | coefficientNormSq c = 1} := by
  have hc : IsClosed {c : Fin m → ℂ | coefficientNormSq c = 1} :=
    isClosed_eq (continuous_coefficientNormSq m) continuous_const
  apply (isCompact_closedBall (0 : Fin m → ℂ) 1).of_isClosed_subset hc
  intro c hc
  simp only [mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (coefficient_norm_le_one hc)

theorem continuous_combination_diskSupNorm {m : ℕ} {g : Fin m → ℂ → ℂ} {r : ℝ}
    (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r)) :
    Continuous (fun c : Fin m → ℂ => diskSupNorm (fun z => ∑ j, c j * g j z) r) := by
  let D := closedBall (0 : ℂ) r
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) r)
  have hc : Continuous (fun p : (Fin m → ℂ) × D => ‖∑ j, p.1 j * g j p.2‖) := by
    apply Continuous.norm
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply j).comp continuous_fst).mul ((hg j).domRestrict.comp continuous_snd)
  have hsup := (isCompact_univ : IsCompact (univ : Set D)).continuous_sSup
    (f := fun (c : Fin m → ℂ) (z : D) => ‖∑ j, c j * g j z‖) hc
  convert hsup using 1
  funext c
  unfold diskSupNorm
  congr 1
  ext v
  simp only [mem_image, mem_univ, true_and, Subtype.exists]
  aesop

/-- The least combination norm is achieved by an actual unit coefficient vector. -/
theorem leastCombinationNorm_attained {m : ℕ} (hm : 0 < m) {g : Fin m → ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hg : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) r)) :
    ∃ c : Fin m → ℂ, coefficientNormSq c = 1 ∧
      leastCombinationNorm g r = diskSupNorm (fun z => ∑ j, c j * g j z) r := by
  let j : Fin m := ⟨0, hm⟩
  obtain ⟨c, hc, hmin⟩ := (coefficient_sphere_isCompact m).exists_isMinOn
    ⟨Pi.single j 1, coefficientNormSq_single j⟩ (continuous_combination_diskSupNorm hg).continuousOn
  refine ⟨c, hc, le_antisymm (leastCombinationNorm_le hr hg c hc) ?_⟩
  apply le_csInf
  · exact ⟨_, c, hc, rfl⟩
  · rintro v ⟨d, hd, rfl⟩
    exact hmin hd

theorem unit_coefficients_have_maximum {m : ℕ} (hm : 0 < m) {c : Fin m → ℂ}
    (hc : coefficientNormSq c = 1) :
    ∃ j : Fin m, (∀ i, ‖c i‖ ≤ ‖c j‖) ∧ 0 < ‖c j‖ ∧
      1 ≤ (m : ℝ) * ‖c j‖ ^ 2 ∧ ∀ i, ‖1 - c i / c j‖ ≤ 2 := by
  classical
  let j₀ : Fin m := ⟨0, hm⟩
  obtain ⟨j, _hj, hjmax⟩ := Finset.exists_max_image Finset.univ (fun i => ‖c i‖)
    ⟨j₀, Finset.mem_univ j₀⟩
  have hmax : ∀ i, ‖c i‖ ≤ ‖c j‖ := fun i => hjmax i (Finset.mem_univ i)
  have hsum : 1 ≤ (m : ℝ) * ‖c j‖ ^ 2 := by
    calc
      _ = ∑ i, ‖c i‖ ^ 2 := hc.symm
      _ ≤ ∑ _i : Fin m, ‖c j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (hmax i) _
      _ = _ := by simp
  have hjpos : 0 < ‖c j‖ := by
    by_contra hn
    have hz : ‖c j‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    norm_num [hz] at hsum
  refine ⟨j, hmax, hjpos, hsum, ?_⟩
  intro i
  have hdiv : ‖c i / c j‖ ≤ 1 := by
    rw [norm_div]
    exact (div_le_one hjpos).mpr (hmax i)
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖c i / c j‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

end ModifiedCartan
