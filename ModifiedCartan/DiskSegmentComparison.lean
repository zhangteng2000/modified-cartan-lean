import ModifiedCartan.SymmetricDiskSegments
import ModifiedCartan.TwoPointHarnack

noncomputable section
set_option autoImplicit false
open Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

/-- Uniform harmonic comparison on an explicitly constructed segment with any
two endpoints whose pseudohyperbolic distance has the prescribed strict bound. -/
theorem disk_segment_harmonic_comparison {q : ℝ} (hq : 0 < q) (hqr : q < sharpRadius) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a b : ℂ), a ∈ disk 1 → b ∈ disk 1 →
      ‖diskAutomorphism a b‖ ≤ symmetricPseudodistance q →
      ∃ t : ℝ, ∃ ξ : ℂ, 0 ≤ t ∧ t ≤ q ∧ ‖ξ‖ = 1 ∧
        diskSegmentMap a ξ t ((-t : ℝ) : ℂ) = a ∧ diskSegmentMap a ξ t (t : ℂ) = b ∧
        ∀ (U P Q : ℂ → ℝ) (C₀ : ℝ),
          HarmonicOnNhd U (disk 1) → HarmonicOnNhd P (disk 1) → HarmonicOnNhd Q (disk 1) →
          (∀ z ∈ disk 1, 0 < U z) → (∀ z ∈ disk 1, 0 ≤ P z) → (∀ z ∈ disk 1, 0 ≤ Q z) →
          0 ≤ C₀ → U a - C₀ ≤ Q a → U b - C₀ ≤ P b →
          ∀ s : ℝ, |s| ≤ t →
            U (diskSegmentMap a ξ t (s : ℂ)) - P (diskSegmentMap a ξ t (s : ℂ)) -
              Q (diskSegmentMap a ξ t (s : ℂ)) ≤ -ε * U (diskSegmentMap a ξ t (s : ℂ)) + 2 * C₀ := by
  obtain ⟨ε, hε, hcomparison⟩ := real_segment_harmonic_comparison hq hqr
  refine ⟨ε, hε, ?_⟩
  intro a b ha hb hab
  obtain ⟨t, ξ, ht, htq, hξ, hleft, hright⟩ := exists_diskSegmentMap ha hb hq.le hab
  refine ⟨t, ξ, ht, htq, hξ, hleft, hright, ?_⟩
  intro U P Q C₀ hU hP hQ hUpos hPpos hQpos hC hQa hPb s hs
  have han : ‖a‖ < 1 := by simpa [disk] using ha
  have ht1 : |t| < 1 := by rw [abs_of_nonneg ht]; exact htq.trans_lt (hqr.trans sharpRadius_lt_one)
  have hg := diskSegmentMap_analytic han hξ ht1
  have hmap : MapsTo (diskSegmentMap a ξ t) (disk 1) (disk 1) :=
    fun z hz => diskSegmentMap_mem_disk han hξ ht1 hz
  have hQc : (fun z => U (diskSegmentMap a ξ t z)) ((-t : ℝ) : ℂ) - C₀ ≤
      (fun z => Q (diskSegmentMap a ξ t z)) ((-t : ℝ) : ℂ) := by simpa only [hleft] using hQa
  have hPc : (fun z => U (diskSegmentMap a ξ t z)) (t : ℂ) - C₀ ≤
      (fun z => P (diskSegmentMap a ξ t z)) (t : ℂ) := by simpa only [hright] using hPb
  exact hcomparison (fun z => U (diskSegmentMap a ξ t z)) (fun z => P (diskSegmentMap a ξ t z))
    (fun z => Q (diskSegmentMap a ξ t z)) t C₀
    (harmonic_comp_analytic_to_ball hU isOpen_ball hg hmap)
    (harmonic_comp_analytic_to_ball hP isOpen_ball hg hmap)
    (harmonic_comp_analytic_to_ball hQ isOpen_ball hg hmap)
    (fun z hz => hUpos _ (hmap hz)) (fun z hz => hPpos _ (hmap hz)) (fun z hz => hQpos _ (hmap hz))
    ht htq hC hQc hPc s hs

end ModifiedCartan
