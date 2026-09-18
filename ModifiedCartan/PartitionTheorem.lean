import ModifiedCartan.NormalizedParts
import ModifiedCartan.PartitionVanishing

noncomputable section
set_option autoImplicit false
open Filter Topology Set Metric Finset
namespace ModifiedCartan

/-- The partition theorem with the manuscript's explicit epsilon = r_(p-1)^(p-1). -/
theorem partition_at_recursive_radius {p : ℕ} (hp : 3 ≤ p) {K : ℕ → ℝ}
    (hK : WronskianExponents K) (hKm : ∀ m : ℕ, (m : ℝ) ≤ K m) :
    PartitionProperty p (disk (absorptionRadius K (p - 1) ^ (p - 1))) := by
  classical
  let σ := absorptionRadius K (p - 1)
  have hσ : 0 < σ := absorptionRadius_pos hKm _
  have hσ1 : σ < 1 := by
    have hle := absorptionRadius_antitone hKm (show 2 ≤ p - 1 by omega)
    exact hle.trans_lt sharpRadius_lt_one
  intro f hf hs
  obtain ⟨φ, hφ, hq, l, hl, hchoice⟩ := stabilization_lemma (by omega) hf hσ hσ1
  let g := subsequence f φ
  have hg : UnitFamily g := unitFamily_subsequence hf φ
  have hgs : ZeroSum g := zeroSum_subsequence hs φ
  let R := diskQuotientPreorder g hg σ hσ.le hσ1.le
  obtain ⟨D⟩ := exists_dominancePartition (R l)
  have hbig : disk (σ ^ l) ⊆ disk 1 := disk_pow_subset_unit hσ.le hσ1.le l
  have hgu : ∀ j n, IsHolomorphicUnit (g j n) (disk (σ ^ l)) := fun j n =>
    ⟨(hg j n).1.mono hbig, fun z hz => (hg j n).2 z (hbig hz)⟩
  let F : Family D.t := fun i => g (D.representative i)
  let h : Family D.t := normalizedPart g D.assign D.representative
  have hb : ∀ i j, j ∈ assignmentPart D.assign i →
      LocallyBounded (fun n z => g j n z / F i n z) (disk (σ ^ l)) := by
    intro i j hj
    have hh := D.dominates j
    rw [mem_assignmentPart.mp hj] at hh
    exact hh
  have hqa : ∀ i j, HolomorphicLimitOrEscape
      (fun n z => g j n z / F i n z) (disk (σ ^ l)) := fun i j => hq j (D.representative i) ⟨l, hl⟩
  obtain ⟨H, hlim⟩ := normalizedPart_limits hgu D.assign D.representative hb hqa
  have hh : ∀ i n, DifferentiableOn ℂ (h i n) (disk (σ ^ l)) :=
    normalizedPart_holomorphic hgu D.assign D.representative
  have hidentity : ∀ n z, z ∈ disk (σ ^ l) → ∑ i, h i n z * F i n z = 0 := by
    intro n z hz
    exact (normalizedPart_identity (fun j n => (hgu j n).2)
      D.assign D.representative hz).trans (hgs n z (hbig hz))
  have hH0 : ∀ i z, z ∈ disk (σ ^ l) → H i z = 0 := by
    by_cases ht : D.t ≤ 1
    · intro i z hz
      have heqn : ∀ n, h i n z = 0 := by
        intro n
        have hsum := hidentity n z hz
        have heq : (∑ j, h j n z * F j n z) = h i n z * F i n z := by
          apply sum_eq_single i
          · intro j _ hji
            have he : j = i := Fin.ext (by have hj := j.isLt; have hi := i.isLt; omega)
            exact (hji he).elim
          · simp
        rw [heq] at hsum
        exact (mul_eq_zero.mp hsum).resolve_right ((hgu (D.representative i) n).2 z hz)
      have hzero : Tendsto (fun n => h i n z) atTop (𝓝 0) := by
        simpa only [heqn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
      exact tendsto_nhds_unique (compactConvergence_pointwise (hlim i) hz) hzero
    · have ht2 : 2 ≤ D.t := by omega
      have hsep : l + 1 < p ∧ ∀ x y, PreorderMaximal (R l) x → PreorderMaximal (R l) y →
          ¬ ((R l).rel x y ∧ (R l).rel y x) →
          ¬ (R (l + 1)).rel x y ∧ ¬ (R (l + 1)).rel y x := by
        rcases hchoice with hone | hmore
        · have htone : D.t = 1 := D.count.trans hone
          omega
        · exact hmore
      have htp : D.t ≤ p := by rw [D.count]; simpa using maximalClasses_card_le (R l)
      have hr1 : absorptionRadius K (D.t - 1) ≤ 1 := by
        simpa [absorptionRadius] using absorptionRadius_antitone hKm (show 0 ≤ D.t - 1 by omega)
      have hrad : σ ^ (l + 1) ≤ σ ^ l * absorptionRadius K (D.t - 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_left (absorptionRadius_antitone hKm (by omega : D.t - 1 ≤ p - 1))
          (pow_nonneg hσ.le _)
      have he : ∀ i j, i ≠ j → EscapesOnCompact (fun n z => F i n z / F j n z)
          (disk (σ ^ l * absorptionRadius K (D.t - 1))) := by
        intro i j hij
        have hn : ¬ LocallyBounded (fun n z => F i n z / F j n z) (disk (σ ^ (l + 1))) :=
          (hsep.2 _ _ (D.maximal i) (D.maximal j) (D.distinct i j hij)).1
        have hu : disk (σ ^ (l + 1)) ⊆ disk 1 := disk_pow_subset_unit hσ.le hσ1.le _
        have hesc := (holomorphicLimitOrEscape_escape_iff
          (hq (D.representative i) (D.representative j) ⟨l + 1, hsep.1⟩)
          (fun n => (((hg (D.representative i) n).1.div (hg (D.representative j) n).1
            (hg (D.representative j) n).2).continuousOn).mono hu)).mpr hn
        obtain ⟨L, hL, hLc, hne, hlimL⟩ := hesc
        exact ⟨L, hL.trans (ball_subset_ball hrad), hLc, hne, hlimL⟩
      exact normalized_limits_zero_of_pairwise_escape ht2 (pow_pos hσ _) hr1
        (absorption_at_recursive_radius hK hKm _ (by omega)) F h H
        (fun i => hgu (D.representative i)) hh hlim hidentity he
  obtain ⟨P⟩ := cpartition_of_assignment D.assign (fun i =>
    ⟨D.representative i, mem_assignmentPart.mpr (D.fixed i), hb i,
      compactConvergence_zero_of_limit_zero (hlim i) (hH0 i)⟩)
  have hsmall : disk (σ ^ (p - 1)) ⊆ disk (σ ^ l) :=
    ball_subset_ball (pow_le_pow_of_le_one hσ.le hσ1.le (by omega))
  refine ⟨φ, hφ, ⟨?_⟩⟩
  exact { parts := P.parts
          cover := P.cover
          disjoint := P.disjoint
          classes := fun I hI => cclass_mono (P.classes I hI) hsmall }

theorem partitionTheorem_proved : PartitionTheorem := by
  obtain ⟨K, _hK0, _hK1, hK, hKm⟩ := exists_wronskianExponents
  intro p hp
  let σ := absorptionRadius K (p - 1)
  have hσ : 0 < σ := absorptionRadius_pos hKm _
  have hσ1 : σ < 1 := (absorptionRadius_antitone hKm (show 2 ≤ p - 1 by omega)).trans_lt sharpRadius_lt_one
  refine ⟨σ ^ (p - 1), pow_pos hσ _, ?_, partition_at_recursive_radius hp hK hKm⟩
  exact pow_lt_one₀ hσ.le hσ1 (by omega)

end ModifiedCartan
