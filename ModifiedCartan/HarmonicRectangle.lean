import ModifiedCartan.HarmonicNegativeNeighborhood
import ModifiedCartan.SegmentNeighborhood

noncomputable section
set_option autoImplicit false
open Filter Topology Complex InnerProductSpace Metric Set
namespace ModifiedCartan

/-- Negativity along converging symmetric segments yields one fixed open
rectangle with a negative linear growth bound. -/
theorem harmonic_negative_rectangle {q ε c C T : ℝ} {t M : ℕ → ℝ}
    {U V : ℕ → ℂ → ℝ} (hq1 : q < 1) (hε : 0 < ε) (hC : 0 ≤ C)
    (hT : T ≤ q) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ q) (hlim : Tendsto t atTop (𝓝 T))
    (hU : ∀ n, HarmonicOnNhd (U n) (disk 1)) (hV : ∀ n, HarmonicOnNhd (V n) (disk 1))
    (hUpos : ∀ n z, z ∈ disk 1 → 0 ≤ U n z) (hVpos : ∀ n z, z ∈ disk 1 → 0 ≤ V n z)
    (hsegment : ∀ᶠ n in atTop, ∀ s : ℝ, |s| ≤ t n →
      c * M n ≤ U n (s : ℂ) ∧ U n (s : ℂ) - V n (s : ℂ) ≤ -ε * U n (s : ℂ) + C) :
    ∃ h : ℝ, 0 < h ∧ T + 2 * h < 1 ∧
      ∀ᶠ n in atTop, ∀ z ∈ segmentRectangle T h,
        U n z - V n z ≤ -(ε * c / 2) * M n + C := by
  obtain ⟨δ, hδ, hδq, hneighborhood⟩ := harmonic_negative_neighborhood_unit hq1 hε
  let h := δ / 4
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : T + 2 * h < 1 := by dsimp [h]; linarith
  refine ⟨h, hh, hh1, ?_⟩
  filter_upwards [hsegment, segmentRectangle_eventually_near hh (fun n => (ht n).1) hlim] with n hn hnear
  intro z hz
  obtain ⟨s, hs, hsz⟩ := hnear z hz
  have hsq : ‖(s : ℂ)‖ ≤ q := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hs.trans (ht n).2
  have hsd : ‖z - (s : ℂ)‖ ≤ δ := hsz.le.trans (by dsimp [h]; linarith)
  have hnz := (hneighborhood (U n) (V n) C (hU n) (hV n) (hUpos n) (hVpos n)
    hC (s : ℂ) hsq (hn s hs).2 z hsd).2
  have hmul := mul_le_mul_of_nonneg_left (hn s hs).1 (half_pos hε).le
  nlinarith

end ModifiedCartan
