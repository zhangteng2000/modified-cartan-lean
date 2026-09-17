import ModifiedCartan.Basic

noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators
namespace ModifiedCartan

theorem locallyBounded_mono {g : ℕ → ℂ → ℂ} {U V : Set ℂ}
    (hg : LocallyBounded g U) (hVU : V ⊆ U) : LocallyBounded g V :=
  fun K hK hcompact => hg K (hK.trans hVU) hcompact

theorem locallyBounded_subsequence {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : LocallyBounded g U) (φ : ℕ → ℕ) : LocallyBounded (fun n => g (φ n)) U := by
  intro K hK hcompact
  obtain ⟨C, hC⟩ := hg K hK hcompact
  exact ⟨C, fun n z hz => hC (φ n) z hz⟩

theorem locallyBounded_congr {g g' : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : LocallyBounded g U) (heq : ∀ n z, z ∈ U → g n z = g' n z) : LocallyBounded g' U := by
  intro K hK hcompact
  obtain ⟨C, hC⟩ := hg K hK hcompact
  exact ⟨C, fun n z hz => by rw [← heq n z (hK hz)]; exact hC n z hz⟩

theorem locallyBounded_mul {g h : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : LocallyBounded g U) (hh : LocallyBounded h U) :
    LocallyBounded (fun n z => g n z * h n z) U := by
  intro K hK hcompact
  obtain ⟨C, hC⟩ := hg K hK hcompact
  obtain ⟨D, hD⟩ := hh K hK hcompact
  refine ⟨max C 0 * max D 0, ?_⟩
  intro n z hz
  rw [norm_mul]
  exact mul_le_mul ((hC n z hz).trans (le_max_left ..))
    ((hD n z hz).trans (le_max_left ..)) (norm_nonneg _) (le_max_right ..)

theorem compactConvergence_subsequence {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hg : CompactConvergence g h U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    CompactConvergence (fun n => g (φ n)) h U := by
  intro K hK hcompact
  exact (hg K hK hcompact).seq_tendstoUniformlyOn φ hφ.tendsto_atTop

theorem compactConvergence_congr {g g' : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hg : CompactConvergence g h U) (heq : ∀ n z, z ∈ U → g n z = g' n z) :
    CompactConvergence g' h U := by
  intro K hK hcompact
  exact (hg K hK hcompact).congr (Eventually.of_forall fun n z hz => heq n z (hK hz))

/-- Multiplication by a locally bounded family preserves locally uniform convergence to zero. -/
theorem compactConvergence_zero_mul {g h : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : CompactConvergence g (fun _ => 0) U) (hh : LocallyBounded h U) :
    CompactConvergence (fun n z => g n z * h n z) (fun _ => 0) U := by
  intro K hK hcompact
  obtain ⟨C, hC⟩ := hh K hK hcompact
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hg K hK hcompact))
    (ε / B) (div_pos hε hB)] with n hn
  intro z hz
  have hgε : ‖g n z‖ < ε / B := by simpa using hn z hz
  have hhB : ‖h n z‖ ≤ B := (hC n z hz).trans (by dsimp [B]; linarith [le_max_left C 0])
  simpa only [dist_zero_left, norm_mul] using
    (mul_le_mul_of_nonneg_left hhB (norm_nonneg (g n z))).trans_lt
      ((lt_div_iff₀ hB).mp hgε)

/-- Every finite list of hereditary extraction requirements can be satisfied together. -/
theorem finite_subsequence_selection {ι : Type*} [Fintype ι]
    (P : ι → (ℕ → ℕ) → Prop)
    (hereditary : ∀ i (φ ψ : ℕ → ℕ), StrictMono φ → StrictMono ψ → P i φ → P i (φ ∘ ψ))
    (extract : ∀ i (φ : ℕ → ℕ), StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, P i φ := by
  classical
  have hfinite : ∀ S : Finset ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ S, P i φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨φ, hφ, hP⟩ := ih
      obtain ⟨ψ, hψ, hiP⟩ := extract i φ hφ
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiP
      · exact hereditary j φ ψ hφ hψ (hP j hj)
  obtain ⟨φ, hφ, hP⟩ := hfinite Finset.univ
  exact ⟨φ, hφ, fun i => hP i (Finset.mem_univ i)⟩

theorem unitFamily_subsequence {p : ℕ} {f : Family p} (hf : UnitFamily f) (φ : ℕ → ℕ) :
    UnitFamily (subsequence f φ) := fun i n => hf i (φ n)

theorem zeroSum_subsequence {p : ℕ} {f : Family p} (hf : ZeroSum f) (φ : ℕ → ℕ) :
    ZeroSum (subsequence f φ) := fun n z hz => hf (φ n) z hz

theorem subsequence_comp {p : ℕ} (f : Family p) (φ ψ : ℕ → ℕ) :
    subsequence (subsequence f φ) ψ = subsequence f (φ ∘ ψ) := rfl

theorem dominant_subsequence {p : ℕ} {f : Family p} {I : Finset (Fin p)} {U : Set ℂ}
    {k : Fin p} (hk : IsDominant f I U k) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsDominant (subsequence f φ) I U k :=
  ⟨hk.1, fun j hj => locallyBounded_subsequence (hk.2.1 j hj) φ,
    compactConvergence_subsequence hk.2.2 hφ⟩

theorem cclass_subsequence {p : ℕ} {f : Family p} {I : Finset (Fin p)} {U : Set ℂ}
    (hI : IsCClass f I U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsCClass (subsequence f φ) I U := by
  obtain ⟨k, hk⟩ := hI
  exact ⟨k, dominant_subsequence hk hφ⟩

theorem cpartition_subsequence {p : ℕ} {f : Family p} {U : Set ℂ}
    (P : CPartition f U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Nonempty (CPartition (subsequence f φ) U) :=
  ⟨{ parts := P.parts
     cover := P.cover
     disjoint := P.disjoint
     classes := fun I hI => cclass_subsequence (P.classes I hI) hφ }⟩

theorem quotient_bounded_refl {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : ∀ n z, z ∈ U → g n z ≠ 0) :
    LocallyBounded (fun n z => g n z / g n z) U := by
  intro K hK _
  exact ⟨1, fun n z hz => by simp [hg n z (hK hz)]⟩

theorem quotient_bounded_trans {f g h : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : ∀ n z, z ∈ U → g n z ≠ 0)
    (hfg : LocallyBounded (fun n z => f n z / g n z) U)
    (hgh : LocallyBounded (fun n z => g n z / h n z) U) :
    LocallyBounded (fun n z => f n z / h n z) U := by
  apply locallyBounded_congr (locallyBounded_mul hfg hgh)
  intro n z hz
  field_simp [hg n z hz]

/-- Change the dominant index precisely when the reverse quotient is locally bounded. -/
theorem dominant_change_index {p : ℕ} {f : Family p} {I : Finset (Fin p)} {U : Set ℂ}
    (hf : ∀ i n z, z ∈ U → f i n z ≠ 0) {k l : Fin p}
    (hk : IsDominant f I U k) (hl : l ∈ I)
    (hkl : LocallyBounded (fun n z => f k n z / f l n z) U) :
    IsDominant f I U l := by
  refine ⟨hl, fun j hj => quotient_bounded_trans (hf k) (hk.2.1 j hj) hkl, ?_⟩
  apply compactConvergence_congr (compactConvergence_zero_mul hk.2.2 hkl)
  intro n z hz
  simp only [← Finset.sum_div]
  field_simp [hf k n z hz, hf l n z hz]

theorem dominant_iff_reverse_quotient_bounded {p : ℕ} {f : Family p}
    {I : Finset (Fin p)} {U : Set ℂ} (hf : ∀ i n z, z ∈ U → f i n z ≠ 0)
    {k l : Fin p} (hk : IsDominant f I U k) (hl : l ∈ I) :
    IsDominant f I U l ↔ LocallyBounded (fun n z => f k n z / f l n z) U :=
  ⟨fun h => h.2.1 k hk.1, dominant_change_index hf hk hl⟩

/-- Uniform limits on compact sets of continuous functions form a locally bounded family,
including the finitely many initial terms. -/
theorem compactConvergence_locallyBounded {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hg : CompactConvergence g h U) (hc : ∀ n, ContinuousOn (g n) U) : LocallyBounded g U := by
  classical
  intro K hK hcompact
  have hu := hg K hK hcompact
  have hh : ContinuousOn h K :=
    hu.continuousOn (Eventually.of_forall fun n => (hc n).mono hK).frequently
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hh
  have hbounds : ∀ n, ∃ C : ℝ, ∀ z ∈ K, ‖g n z‖ ≤ C :=
    fun n => hcompact.exists_bound_of_continuousOn ((hc n).mono hK)
  choose C hC using hbounds
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hu 1 (by norm_num))
  let A := ∑ n ∈ Finset.range N, max (C n) 0
  have hA : 0 ≤ A := Finset.sum_nonneg (fun n _ => le_max_right (C n) 0)
  refine ⟨max B 0 + 1 + A, ?_⟩
  intro n z hz
  by_cases hn : N ≤ n
  · have hd : ‖g n z - h z‖ < 1 := by
      simpa [dist_eq_norm, norm_sub_rev] using hN n hn z hz
    have hb : ‖g n z‖ ≤ B + 1 := by
      calc
        _ = ‖h z + (g n z - h z)‖ := by congr 1; ring
        _ ≤ ‖h z‖ + ‖g n z - h z‖ := norm_add_le _ _
        _ ≤ B + 1 := add_le_add (hB z hz) hd.le
    exact hb.trans (by linarith [le_max_left B 0])
  · have hn' : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hnA : max (C n) 0 ≤ A :=
      Finset.single_le_sum (fun i _ => le_max_right (C i) 0) hn'
    exact ((hC n z hz).trans (le_max_left ..)).trans
      (hnA.trans (by linarith [le_max_right B 0]))

theorem compactConvergence_holomorphic {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : CompactConvergence g h U)
    (hd : ∀ n, DifferentiableOn ℂ (g n) U) : DifferentiableOn ℂ h U :=
  ((compactConvergence_iff hU).mp hg).differentiableOn (Eventually.of_forall hd) hU

theorem compactConvergence_deriv {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : CompactConvergence g h U)
    (hd : ∀ n, DifferentiableOn ℂ (g n) U) :
    CompactConvergence (fun n => deriv (g n)) (deriv h) U :=
  (compactConvergence_iff hU).mpr
    (((compactConvergence_iff hU).mp hg).deriv (Eventually.of_forall hd) hU)

end ModifiedCartan
