import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic

/-! Definitions from Section 1. No assertion of the paper is assumed. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace ModifiedCartan

def disk (r : ℝ) : Set ℂ := Metric.ball 0 r

def IsHolomorphicUnit (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ ∀ z ∈ U, f z ≠ 0

abbrev Family (p : ℕ) := Fin p → ℕ → ℂ → ℂ

def UnitFamily {p : ℕ} (f : Family p) : Prop :=
  ∀ i n, IsHolomorphicUnit (f i n) (disk 1)

def ZeroSum {p : ℕ} (f : Family p) : Prop :=
  ∀ n z, z ∈ disk 1 → ∑ i, f i n z = 0

def LocallyBounded (g : ℕ → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∃ C : ℝ, ∀ n z, z ∈ K → ‖g n z‖ ≤ C

def CompactConvergence (g : ℕ → ℂ → ℂ) (h : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K : Set ℂ, K ⊆ U → IsCompact K → TendstoUniformlyOn g h atTop K

theorem compactConvergence_iff {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) :
    CompactConvergence g h U ↔ TendstoLocallyUniformlyOn g h atTop U := by
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).symm

theorem compactConvergence_mono {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U V : Set ℂ}
    (hg : CompactConvergence g h U) (hVU : V ⊆ U) : CompactConvergence g h V := by
  intro K hK hcompact
  exact hg K (hK.trans hVU) hcompact

theorem compactConvergence_pointwise {g : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {U : Set ℂ}
    (hg : CompactConvergence g h U) {z : ℂ} (hz : z ∈ U) :
    Tendsto (fun n => g n z) atTop (𝓝 (h z)) := by
  exact (hg {z} (Set.singleton_subset_iff.mpr hz) isCompact_singleton).tendsto_at (by simp)

def IsDominant {p : ℕ} (f : Family p) (I : Finset (Fin p)) (U : Set ℂ) (k : Fin p) : Prop :=
  k ∈ I ∧ (∀ j ∈ I, LocallyBounded (fun n z => f j n z / f k n z) U) ∧
  CompactConvergence (fun n z => ∑ j ∈ I, f j n z / f k n z) (fun _ => 0) U

def IsCClass {p : ℕ} (f : Family p) (I : Finset (Fin p)) (U : Set ℂ) : Prop :=
  ∃ k, IsDominant f I U k

structure CPartition {p : ℕ} (f : Family p) (U : Set ℂ) where
  parts : Finset (Finset (Fin p))
  cover : ∀ i, ∃ I ∈ parts, i ∈ I
  disjoint : ∀ I ∈ parts, ∀ J ∈ parts, I ≠ J → Disjoint I J
  classes : ∀ I ∈ parts, IsCClass f I U

def subsequence {p : ℕ} (f : Family p) (φ : ℕ → ℕ) : Family p :=
  fun i n => f i (φ n)

theorem cclass_nonempty {p : ℕ} {f : Family p} {I : Finset (Fin p)} {U : Set ℂ}
    (h : IsCClass f I U) : I.Nonempty := by
  obtain ⟨k, hk, _⟩ := h
  exact ⟨k, hk⟩

theorem cclass_mono {p : ℕ} {f : Family p} {I : Finset (Fin p)} {U V : Set ℂ}
    (h : IsCClass f I U) (hVU : V ⊆ U) : IsCClass f I V := by
  obtain ⟨k, hk, hb, hc⟩ := h
  refine ⟨k, hk, ?_, compactConvergence_mono hc hVU⟩
  intro j hj K hK hcompact
  exact hb j hj K (hK.trans hVU) hcompact

theorem cclass_card_ge_two {p : ℕ} {f : Family p} {I : Finset (Fin p)}
    {U : Set ℂ} (hU : U.Nonempty) (hf : ∀ i n z, z ∈ U → f i n z ≠ 0)
    (h : IsCClass f I U) : 2 ≤ I.card := by
  obtain ⟨k, hk, _, hc⟩ := h
  by_contra hcard
  have hsingle : I = {k} := by
    have hle : I.card ≤ 1 := by omega
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hk, fun j hj => (Finset.card_le_one.mp hle) j hj k hk⟩
  obtain ⟨z, hz⟩ := hU
  have ht := compactConvergence_pointwise hc hz
  have heq : (fun n => ∑ j ∈ I, f j n z / f k n z) = fun _ => (1 : ℂ) := by
    funext n
    simp [hsingle, hf k n z hz]
  rw [heq] at ht
  have : (1 : ℂ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  exact one_ne_zero this

def PartitionProperty (p : ℕ) (U : Set ℂ) : Prop :=
  ∀ f : Family p, UnitFamily f → ZeroSum f →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Nonempty (CPartition (subsequence f φ) U)

theorem partitionProperty_mono {p : ℕ} {U V : Set ℂ}
    (h : PartitionProperty p U) (hVU : V ⊆ U) : PartitionProperty p V := by
  intro f hf hs
  obtain ⟨φ, hφ, ⟨P⟩⟩ := h f hf hs
  refine ⟨φ, hφ, ⟨?_⟩⟩
  exact { parts := P.parts
          cover := P.cover
          disjoint := P.disjoint
          classes := fun I hI => cclass_mono (P.classes I hI) hVU }

end ModifiedCartan
