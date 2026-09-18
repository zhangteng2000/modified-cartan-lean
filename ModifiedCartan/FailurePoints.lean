import ModifiedCartan.Convergence
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- Diagonal extraction on a compact exhaustion of any open complex set. -/
theorem compactConvergence_zero_subsequence_of_frequently_small {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hsmall : ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ ∀ z ∈ K, ‖g n z‖ < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence (fun n => g (φ n)) (fun _ => 0) U := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  have hex : ∀ k N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ z ∈ K k, ‖g n (z : ℂ)‖ < 1 / (k + 1 : ℝ) := by
    intro k N
    obtain ⟨n, hn, hb⟩ := hsmall (Subtype.val '' K k)
      (by rintro _ ⟨z, _, rfl⟩; exact z.property)
      ((K.isCompact k).image continuous_subtype_val) (1 / (k + 1 : ℝ)) (by positivity) N
    exact ⟨n, hn, fun z hz => hb z (mem_image_of_mem _ hz)⟩
  choose f hf hfsmall using hex
  let φ : ℕ → ℕ := fun n => Nat.rec (f 0 0) (fun k prev => f (k + 1) (prev + 1)) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change φ n < f (n + 1) (φ n + 1)
    exact (Nat.lt_succ_self _).trans_le (hf _ _)
  have hφsmall : ∀ n, ∀ z ∈ K n, ‖g (φ n) (z : ℂ)‖ < 1 / (n + 1 : ℝ) := by
    intro n
    cases n with
    | zero => exact hfsmall 0 0
    | succ n => exact hfsmall (n + 1) (φ n + 1)
  refine ⟨φ, hφ, (compactConvergence_iff hU).mpr ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro w
  obtain ⟨k, hk⟩ := K.exists_mem_nhds w
  refine ⟨K k, hk, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) < ε :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop k, he] with n hn hnε
  intro z hz
  simpa only [Function.comp_apply, dist_zero_left] using
    (hφsmall n z (K.subset hn hz)).trans hnε

/-- Failure of every zero-convergent subsequence forces a uniform obstruction
on one fixed compact set. No connectedness is required. -/
theorem reciprocal_failure_compact {g : ℕ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence (fun n => g (φ n)) (fun _ => 0) U) :
    ∃ K : Set ℂ, K ⊆ U ∧ IsCompact K ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n in atTop, ∃ z ∈ K, ε ≤ ‖g n z‖ := by
  by_contra hfail
  apply hno
  apply compactConvergence_zero_subsequence_of_frequently_small hU
  intro K hKU hK ε hε N
  by_contra h
  push Not at h
  apply hfail
  refine ⟨K, hKU, hK, ε, hε, eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro n hn
  exact h n hn

/-- The failure points for a unit family have uniformly bounded logarithmic modulus. -/
theorem unit_failure_points {A : ℕ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hA : ∀ n z, z ∈ U → A n z ≠ 0)
    (hno : ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence
      (fun n z => (A (φ n) z)⁻¹) (fun _ => 0) U) :
    ∃ K : Set ℂ, K ⊆ U ∧ IsCompact K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∃ z ∈ K, Real.log ‖A n z‖ ≤ C := by
  obtain ⟨K, hKU, hK, ε, hε, hf⟩ := reciprocal_failure_compact (g := fun n z => (A n z)⁻¹) hU hno
  refine ⟨K, hKU, hK, max 0 (Real.log (1 / ε)), le_max_left _ _, ?_⟩
  filter_upwards [hf] with n hn
  obtain ⟨z, hz, hnorm⟩ := hn
  refine ⟨z, hz, ?_⟩
  have hAz : 0 < ‖A n z‖ := norm_pos_iff.mpr (hA n z (hKU hz))
  have hbound : ‖A n z‖ ≤ 1 / ε := by
    rw [norm_inv, ← one_div] at hnorm
    apply (le_div_iff₀ hε).mpr
    nlinarith [(le_div_iff₀ hAz).mp hnorm]
  exact (Real.log_le_log hAz hbound).trans (le_max_right _ _)

end ModifiedCartan
