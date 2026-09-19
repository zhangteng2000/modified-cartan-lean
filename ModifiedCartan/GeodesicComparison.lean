import ModifiedCartan.HyperbolicSegments
import ModifiedCartan.DiskSegmentComparison

noncomputable section
set_option autoImplicit false
open Complex InnerProductSpace Metric Set Real
namespace ModifiedCartan

/-- Manuscript `cor:geodesic-comparison`, on the full hyperbolic segment and
with one positive constant uniform in the endpoints and harmonic functions. -/
theorem geodesic_harmonic_comparison {d₀ : ℝ} (hd₀ : 0 < d₀) (hd₃ : d₀ < Real.log 3) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (a b : ℂ), a ∈ disk 1 → b ∈ disk 1 →
      hyperbolicDistance a b ≤ d₀ → ∀ (U P Q : ℂ → ℝ) (C₀ : ℝ),
        HarmonicOnNhd U (disk 1) → HarmonicOnNhd P (disk 1) → HarmonicOnNhd Q (disk 1) →
        (∀ z ∈ disk 1, 0 < U z) → (∀ z ∈ disk 1, 0 ≤ P z) → (∀ z ∈ disk 1, 0 ≤ Q z) →
        0 ≤ C₀ → U a - C₀ ≤ Q a → U b - C₀ ≤ P b →
        ∀ z ∈ hyperbolicSegment a b, U z - P z - Q z ≤ -ε * U z + 2 * C₀ := by
  obtain ⟨q, hq, hqr, hbound⟩ := distance_bound_uniform_pseudoradius hd₀ hd₃
  obtain ⟨ε, hε, hcomparison⟩ := disk_segment_harmonic_comparison hq hqr
  refine ⟨ε, hε, ?_⟩
  intro a b ha hb hab U P Q C₀ hU hP hQ hUpos hPpos hQpos hC hQa hPb z hz
  obtain ⟨t, ξ, ht0, htq, hξ, hleft, hright, hestimate⟩ :=
    hcomparison a b ha hb (hbound a b ha hb hab)
  have han : ‖a‖ < 1 := by simpa [disk] using ha
  have ht : |t| < 1 := by
    rw [abs_of_nonneg ht0]
    exact htq.trans_lt (hqr.trans sharpRadius_lt_one)
  have himage := hyperbolicSegment_diskSegmentMap han hξ ht0 ht
  rw [hleft, hright] at himage
  rw [himage] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  exact hestimate U P Q C₀ hU hP hQ hUpos hPpos hQpos hC hQa hPb s (abs_le.mpr hs)

end ModifiedCartan
