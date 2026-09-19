import ModifiedCartan.Convergence

noncomputable section
set_option autoImplicit false
open Complex Metric Set Filter Topology
namespace ModifiedCartan

/-- A constant coordinate cannot join coordinates which diverge at a common
point and individually vanish at other points. The obstruction survives every
subsequence. All analytic asymptotics are genuine hypotheses of this auxiliary
lemma; the counterexample modules separately prove them for the explicit family. -/
theorem constant_coordinate_partition_obstruction {p : ℕ} {f : Family p} {U : Set ℂ}
    (hf : ∀ i n z, z ∈ U → f i n z ≠ 0) (k : Fin p) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hconst : ∀ n z, z ∈ U → f k n z = -1)
    (hlarge : ∀ j, j ≠ k → Tendsto (fun n => ‖f j n z₀‖) atTop atTop)
    (hsmall : ∀ j, j ≠ k → ∃ z ∈ U, Tendsto (fun n => f j n z) atTop (𝓝 0))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : ¬ Nonempty (CPartition (subsequence f φ) U) := by
  classical
  rintro ⟨P⟩
  obtain ⟨I, hIP, hkI⟩ := P.cover k
  have hclass := P.classes I hIP
  have hcard := cclass_card_ge_two (show U.Nonempty from ⟨z₀, hz₀⟩)
    (fun i n z hz => hf i (φ n) z hz) hclass
  obtain ⟨j, hjI, hbounded, _hsum⟩ := hclass
  by_cases hjk : j = k
  · subst j
    obtain ⟨l, hlI, hlk⟩ : ∃ l ∈ I, l ≠ k := by
      by_contra hh
      push Not at hh
      have hsub : I ⊆ {k} := fun l hl => by simpa using hh l hl
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hc
      omega
    obtain ⟨C, hC⟩ := hbounded l hlI {z₀} (singleton_subset_iff.mpr hz₀) isCompact_singleton
    have hlim := (hlarge l hlk).comp hφ.tendsto_atTop
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_atTop C)).exists
    have hbound := hC n z₀ (mem_singleton z₀)
    have hb : ‖f l (φ n) z₀‖ ≤ C := by
      simpa only [subsequence, hconst (φ n) z₀ hz₀, norm_div, norm_neg, norm_one, div_one] using hbound
    exact (not_le_of_gt hn) hb
  · obtain ⟨z, hz, hzero⟩ := hsmall j hjk
    obtain ⟨C, hC⟩ := hbounded k hkI {z} (singleton_subset_iff.mpr hz) isCompact_singleton
    have hn (n : ℕ) : 1 ≤ C * ‖f j (φ n) z‖ := by
      have hb := mul_le_mul_of_nonneg_right (hC n z (mem_singleton z)) (norm_nonneg (f j (φ n) z))
      have hnorm : ‖f j (φ n) z‖ ≠ 0 := norm_ne_zero_iff.mpr (hf j (φ n) z hz)
      simpa only [subsequence, hconst (φ n) z hz, norm_div, norm_neg, norm_one,
        one_div, inv_mul_cancel₀ hnorm] using hb
    have hlim := ((hzero.comp hφ.tendsto_atTop).norm).const_mul C
    have hh := ge_of_tendsto hlim (Eventually.of_forall hn)
    norm_num at hh

end ModifiedCartan
