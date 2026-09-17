import ModifiedCartan.Montel

noncomputable section
set_option autoImplicit false
open Filter Topology Set
namespace ModifiedCartan

theorem unbounded_real_subsequence {u : ℕ → ℝ} (hu : ¬ BddAbove (range u)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop atTop := by
  classical
  have htail : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (N : ℝ) ≤ u n := by
    intro N
    obtain ⟨A, hA⟩ := ((Finset.range N).finite_toSet.image u).bddAbove
    obtain ⟨v, ⟨n, rfl⟩, hv⟩ := not_bddAbove_iff.mp hu (max A (N : ℝ))
    refine ⟨n, ?_, (le_max_right A _).trans hv.le⟩
    by_contra hn
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hle := hA (mem_image_of_mem u hnN)
    linarith [le_max_left A (N : ℝ)]
  choose v hvN hvu using htail
  have hv : Tendsto v atTop atTop := tendsto_atTop_mono hvN tendsto_id
  have huv : Tendsto (u ∘ v) atTop atTop :=
    tendsto_atTop_mono hvu tendsto_natCast_atTop_atTop
  obtain ⟨ψ, hψ, hvψ⟩ := strictMono_subseq_of_tendsto_atTop hv
  exact ⟨v ∘ ψ, hvψ, huv.comp hψ.tendsto_atTop⟩

def compactSupNorm (f : ℂ → ℂ) (K : Set ℂ) : ℝ := sSup ((fun z => ‖f z‖) '' K)

def EscapesOnCompact (g : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ K : Set ℂ, K ⊆ U ∧ IsCompact K ∧ K.Nonempty ∧
    Tendsto (fun n => compactSupNorm (g n) K) atTop atTop

theorem escapesOnCompact_subsequence {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : EscapesOnCompact g U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    EscapesOnCompact (fun n => g (φ n)) U := by
  obtain ⟨K, hKU, hK, hne, hlim⟩ := hg
  exact ⟨K, hKU, hK, hne, hlim.comp hφ.tendsto_atTop⟩

theorem escapesOnCompact_not_locallyBounded {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : EscapesOnCompact g U) : ¬ LocallyBounded g U := by
  obtain ⟨K, hKU, hK, hne, hlim⟩ := hg
  intro hb
  obtain ⟨C, hC⟩ := hb K hKU hK
  have hsup : ∀ n, compactSupNorm (g n) K ≤ C := by
    intro n
    exact csSup_le (hne.image _) (by rintro v ⟨z, hz, rfl⟩; exact hC n z hz)
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_gt_atTop (C + 1))).exists
  have := hsup n
  linarith

/-- The unbounded alternative uses the actual compact-set supremum, not pointwise divergence. -/
theorem not_locallyBounded_subsequence {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hc : ∀ n, ContinuousOn (g n) U) (hb : ¬ LocallyBounded g U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ EscapesOnCompact (fun n => g (φ n)) U := by
  classical
  dsimp [LocallyBounded] at hb
  push Not at hb
  obtain ⟨K, hKU, hK, hnotbound⟩ := hb
  have hne : K.Nonempty := by
    obtain ⟨n, z, hz, _⟩ := hnotbound 0
    exact ⟨z, hz⟩
  have hbounded : ∀ n, BddAbove ((fun z => ‖g n z‖) '' K) :=
    fun n => (hK.image_of_continuousOn ((hc n).mono hKU).norm).bddAbove
  have hu : ¬ BddAbove (range (fun n => compactSupNorm (g n) K)) := by
    rintro ⟨C, hC⟩
    obtain ⟨n, z, hz, hnz⟩ := hnotbound C
    have hs : ‖g n z‖ ≤ compactSupNorm (g n) K :=
      le_csSup (hbounded n) (mem_image_of_mem (fun z => ‖g n z‖) hz)
    have hle := hC (mem_range_self n)
    linarith
  obtain ⟨φ, hφ, hlim⟩ := unbounded_real_subsequence hu
  exact ⟨φ, hφ, K, hKU, hK, hne, hlim⟩

def HolomorphicLimitOrEscape (g : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  (∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ CompactConvergence g h U) ∨ EscapesOnCompact g U

theorem holomorphicLimitOrEscape_limit_iff {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : HolomorphicLimitOrEscape g U) (hc : ∀ n, ContinuousOn (g n) U) :
    (∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ CompactConvergence g h U) ↔
      LocallyBounded g U := by
  constructor
  · rintro ⟨h, _, hlim⟩
    exact compactConvergence_locallyBounded hlim hc
  · intro hb
    exact hg.resolve_right (fun h => escapesOnCompact_not_locallyBounded h hb)

theorem holomorphicLimitOrEscape_escape_iff {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : HolomorphicLimitOrEscape g U) (hc : ∀ n, ContinuousOn (g n) U) :
    EscapesOnCompact g U ↔ ¬ LocallyBounded g U := by
  refine ⟨escapesOnCompact_not_locallyBounded, ?_⟩
  intro hb
  exact hg.resolve_left (fun h => hb ((holomorphicLimitOrEscape_limit_iff hg hc).mp h))

theorem holomorphicLimitOrEscape_subsequence {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hg : HolomorphicLimitOrEscape g U) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    HolomorphicLimitOrEscape (fun n => g (φ n)) U := by
  rcases hg with ⟨h, hd, hlim⟩ | hescape
  · exact Or.inl ⟨h, hd, compactConvergence_subsequence hlim hφ⟩
  · exact Or.inr (escapesOnCompact_subsequence hescape hφ)

theorem holomorphic_limit_or_escape_subsequence {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hd : ∀ n, DifferentiableOn ℂ (g n) U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ HolomorphicLimitOrEscape (fun n => g (φ n)) U := by
  by_cases hb : LocallyBounded g U
  · obtain ⟨φ, hφ, h, hh, hlim⟩ := montel_subsequence hU hd hb
    exact ⟨φ, hφ, Or.inl ⟨h, hh, hlim⟩⟩
  · obtain ⟨φ, hφ, hescape⟩ := not_locallyBounded_subsequence (fun n => (hd n).continuousOn) hb
    exact ⟨φ, hφ, Or.inr hescape⟩

/-- A single subsequence works for a finite family, including different open domains. -/
theorem finite_holomorphic_limit_or_escape {ι : Type*} [Fintype ι]
    (g : ι → ℕ → ℂ → ℂ) (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hd : ∀ i n, DifferentiableOn ℂ (g i n) (U i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, HolomorphicLimitOrEscape (fun n => g i (φ n)) (U i) := by
  apply finite_subsequence_selection
    (fun i φ => HolomorphicLimitOrEscape (fun n => g i (φ n)) (U i))
  · intro i φ ψ _ hψ h
    exact holomorphicLimitOrEscape_subsequence h hψ
  · intro i φ _
    exact holomorphic_limit_or_escape_subsequence (hU i) (fun n => hd i (φ n))

/-- Simultaneous analytic alternatives for every quotient on finitely many subdomains. -/
theorem unitFamily_quotient_extraction {p q : ℕ} {f : Family p}
    (hf : UnitFamily f) (U : Fin q → Set ℂ) (hU : ∀ k, IsOpen (U k))
    (hsub : ∀ k, U k ⊆ disk 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i j k,
      HolomorphicLimitOrEscape (fun n z => f i (φ n) z / f j (φ n) z) (U k) := by
  obtain ⟨φ, hφ, h⟩ := finite_holomorphic_limit_or_escape
    (fun a : Fin p × Fin p × Fin q => fun n z => f a.1 n z / f a.2.1 n z)
    (fun a => U a.2.2) (fun a => hU a.2.2)
    (fun a n => ((hf a.1 n).1.mono (hsub a.2.2)).div
      ((hf a.2.1 n).1.mono (hsub a.2.2))
      (fun z hz => (hf a.2.1 n).2 z (hsub a.2.2 hz)))
  exact ⟨φ, hφ, fun i j k => h (i, j, k)⟩

end ModifiedCartan
