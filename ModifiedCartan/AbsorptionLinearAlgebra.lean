import ModifiedCartan.CombinationMinimum
import ModifiedCartan.Convergence
import ModifiedCartan.Rescaling

noncomputable section
set_option autoImplicit false
open Filter Metric Set
namespace ModifiedCartan

theorem finite_constant_subsequence {ι : Type*} [Finite ι] (j : ℕ → ι) :
    ∃ i : ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, j (φ n) = i := by
  have hfreq : ∃ i : ι, ∃ᶠ n in atTop, j n = i :=
    frequently_exists.mp (Frequently.of_forall (fun n => ⟨j n, rfl⟩))
  obtain ⟨i, hi⟩ := hfreq
  obtain ⟨φ, hφ, hh⟩ := extraction_of_frequently_atTop hi
  exact ⟨i, φ, hφ, hh⟩

theorem maximal_unit_coefficient_inv_bound {m : ℕ} {c : Fin m → ℂ}
    (hc : coefficientNormSq c = 1) {j : Fin m} (hmax : ∀ i, ‖c i‖ ≤ ‖c j‖) :
    c j ≠ 0 ∧ ‖(c j)⁻¹‖ ≤ (m : ℝ) := by
  have hsum : 1 ≤ (m : ℝ) * ‖c j‖ ^ 2 := by
    calc
      _ = ∑ i, ‖c i‖ ^ 2 := hc.symm
      _ ≤ ∑ _i : Fin m, ‖c j‖ ^ 2 := Finset.sum_le_sum
        (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hmax i) _)
      _ = _ := by simp
  have hj0 : 0 < ‖c j‖ := by
    by_contra hn
    have hz : ‖c j‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    norm_num [hz] at hsum
  refine ⟨norm_pos_iff.mp hj0, ?_⟩
  rw [norm_inv, ← one_div]
  apply (div_le_iff₀ hj0).mpr
  have hj1 := coefficient_norm_le_one hc j
  have hs : ‖c j‖ ^ 2 ≤ ‖c j‖ := by nlinarith [norm_nonneg (c j)]
  nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg m : (0:ℝ) ≤ m)]

theorem remove_one_coefficient_identity {m : ℕ} (a c : Fin (m + 1) → ℂ) (j : Fin (m + 1))
    (hj : c j ≠ 0) :
    ∑ i : Fin m, (1 - c (j.succAbove i) / c j) * a (j.succAbove i) =
      (∑ i, a i) - (∑ i, c i * a i) / c j := by
  have he : (∑ i, (1 - c i / c j) * a i) = (∑ i, a i) - (∑ i, c i * a i) / c j := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Fin.sum_univ_succAbove _ j] at he
  simpa [hj] using he

theorem compactConvergence_sub {g h : ℕ → ℂ → ℂ} {s t : ℂ → ℂ} {U : Set ℂ}
    (hg : CompactConvergence g s U) (hh : CompactConvergence h t U) :
    CompactConvergence (fun n z => g n z - h n z) (fun z => s z - t z) U := by
  intro K hKU hK
  exact (hg K hKU hK).fun_sub (hh K hKU hK)

theorem compactConvergence_zero_of_diskSupNorm {g : ℕ → ℂ → ℂ} {r : ℝ}
    (hg : ∀ n, ContinuousOn (g n) (closedBall (0 : ℂ) r))
    (hlim : Tendsto (fun n => diskSupNorm (g n) r) atTop (nhds 0)) :
    CompactConvergence g (fun _ => 0) (disk r) := by
  intro K hKU _hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  have hzball : z ∈ closedBall (0 : ℂ) r := ball_subset_closedBall (hKU hz)
  have hbound : ‖g n z‖ ≤ diskSupNorm (g n) r :=
    le_csSup ((isCompact_closedBall (0 : ℂ) r).bddAbove_image (hg n).norm)
      (mem_image_of_mem _ hzball)
  simpa only [dist_zero_left] using hbound.trans_lt hn

end ModifiedCartan
