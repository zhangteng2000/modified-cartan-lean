import ModifiedCartan.CClassJets
import ModifiedCartan.SmallPartitions
import ModifiedCartan.Exponential

noncomputable section
set_option autoImplicit false
open Filter Topology Set Finset
namespace ModifiedCartan

theorem cpartition_sum {p : ℕ} {f : Family p} {U : Set ℂ}
    (P : CPartition f U) (b : Fin p → ℂ) :
    ∑ i, b i = ∑ I ∈ P.parts, ∑ i ∈ I, b i := by
  classical
  have hcover : P.parts.biUnion id = Finset.univ := by
    ext i
    constructor
    · intro _; exact mem_univ i
    · intro _
      obtain ⟨I, hI, hi⟩ := P.cover i
      exact mem_biUnion.mpr ⟨I, hI, hi⟩
  rw [← hcover]
  exact sum_biUnion (fun I hI J hJ hne => P.disjoint I hI J hJ hne)

/-- The analytic consequence of the partition theorem used in the torus proof:
limiting values and logarithmic derivative rates annihilate the entire exponential sum. -/
theorem exponentialSum_zero_of_unit_jet_limits {p : ℕ} {f : Family p}
    (hf : UnitFamily f) (hs : ZeroSum f) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) (htpos : ∀ n, 0 < t n)
    (c rate : Fin p → ℂ) (hc : ∀ i, c i ≠ 0)
    (hcenter : ∀ i, Tendsto (fun n => f i n 0) atTop (𝓝 (c i)))
    (hder : ∀ i, Tendsto (fun n => deriv (f i n) 0 / (t n : ℂ)) atTop (𝓝 (c i * rate i))) :
    ∀ z : ℂ, exponentialSum c rate z = 0 := by
  classical
  obtain ⟨r, hr, hr1, hpart⟩ := partition_exists_positive_radius p
  obtain ⟨φ, hφ, ⟨P⟩⟩ := hpart f hf hs
  have hclasses : ∀ I ∈ P.parts, (∑ i ∈ I, c i = 0) ∧
      ∃ k ∈ I, ∀ i ∈ I, rate i = rate k := by
    intro I hI
    obtain ⟨hcanc, k, hk, heq⟩ := cclass_jet_limits hr hr1 (unitFamily_subsequence hf φ)
      (P.classes I hI) (ht.comp hφ.tendsto_atTop) (fun n => htpos (φ n))
      c (fun i => c i * rate i) hc
      (fun i => (hcenter i).comp hφ.tendsto_atTop)
      (fun i => (hder i).comp hφ.tendsto_atTop)
    refine ⟨hcanc, k, hk, ?_⟩
    intro i hi
    simpa only [mul_div_cancel_left₀ _ (hc i), mul_div_cancel_left₀ _ (hc k)] using heq i hi
  intro z
  unfold exponentialSum
  rw [cpartition_sum P]
  apply sum_eq_zero
  intro I hI
  obtain ⟨hcanc, k, _hk, heq⟩ := hclasses I hI
  calc
    _ = ∑ i ∈ I, c i * Complex.exp (rate k * z) := sum_congr rfl (fun i hi => by rw [heq i hi])
    _ = (∑ i ∈ I, c i) * Complex.exp (rate k * z) := (sum_mul ..).symm
    _ = 0 := by rw [hcanc, zero_mul]

end ModifiedCartan
