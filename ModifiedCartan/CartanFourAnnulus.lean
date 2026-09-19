import ModifiedCartan.DiskAnnulusCover
import ModifiedCartan.CompactLifts
import ModifiedCartan.CartanFour
import Mathlib.Analysis.Complex.OpenMapping

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

theorem exists_holomorphic_disk_annulus_cover {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ (disk 1) ∧
      MapsTo ψ (disk 1) (complexAnnulus a b) ∧ SurjOn ψ (disk 1) (complexAnnulus a b) ∧
      ∀ K : Set ℂ, K ⊆ complexAnnulus a b → IsCompact K →
        ∃ L : Set ℂ, L ⊆ disk 1 ∧ IsCompact L ∧ K ⊆ ψ '' L := by
  let ψ := diskAnnulusCover (Real.log a) (Real.log b)
  have hlogs : Real.log a < Real.log b := Real.log_lt_log ha hab
  have hdiff : DifferentiableOn ℂ ψ (disk 1) := diskAnnulusCover_differentiableOn _ _
  have hmap : MapsTo ψ (disk 1) (complexAnnulus a b) := by
    simpa only [Real.exp_log ha,Real.exp_log (ha.trans hab)] using diskAnnulusCover_mapsTo hlogs
  have hsurj : SurjOn ψ (disk 1) (complexAnnulus a b) := by
    simpa only [Real.exp_log ha,Real.exp_log (ha.trans hab)] using diskAnnulusCover_surjOn hlogs
  have hnc : ¬ ∃ c : ℂ, ∀ z ∈ disk 1, ψ z = c := by
    rintro ⟨c,hc⟩
    obtain ⟨w,hw⟩ := complexAnnulus_nonempty ha.le hab
    have hneg : -w ∈ complexAnnulus a b := by
      simpa [complexAnnulus] using hw
    obtain ⟨x,hx,hex⟩ := hsurj hw
    obtain ⟨y,hy,hey⟩ := hsurj hneg
    have he : w = -w := hex.symm.trans ((hc x hx).trans ((hc y hy).symm.trans hey))
    have hwn : w ≠ 0 := norm_pos_iff.mp (ha.trans hw.1)
    apply hwn
    linear_combination (1/2 : ℂ)*he
  have ho := ((hdiff.analyticOnNhd isOpen_ball).is_constant_or_isOpen
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected).resolve_left hnc
  exact ⟨ψ,hdiff,hmap,hsurj,compact_lifts_of_open_surjection isOpen_ball ho hsurj⟩

/-- The four-function theorem on the actual annulus, obtained through an
explicit holomorphic covering and compact lifts. -/
theorem cartan_four_annulus {a b : ℝ} (ha : 0 < a) (hab : a < b) {f : Family 4}
    (hf : ∀ i n, IsHolomorphicUnit (f i n) (complexAnnulus a b))
    (hs : ∀ n z, z ∈ complexAnnulus a b → ∑ i, f i n z = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (IsCClass (subsequence f φ) Finset.univ (complexAnnulus a b) ∨
       ∃ I J : Finset (Fin 4), Disjoint I J ∧
         IsCClass (subsequence f φ) I (complexAnnulus a b) ∧
         IsCClass (subsequence f φ) J (complexAnnulus a b)) := by
  obtain ⟨ψ,hψ,hmap,_,hlift⟩ := exists_holomorphic_disk_annulus_cover ha hab
  let F : Family 4 := fun i n z => f i n (ψ z)
  have hFu : UnitFamily F := fun i n =>
    ⟨(hf i n).1.comp hψ hmap,fun z hz => (hf i n).2 (ψ z) (hmap hz)⟩
  have hFs : ZeroSum F := fun n z hz => hs n (ψ z) (hmap hz)
  obtain ⟨φ,hφ,hc⟩ := cartanExtraction_four F hFu hFs
  refine ⟨φ,hφ,?_⟩
  rcases hc with hfull | ⟨I,J,hd,hI,hJ⟩
  · exact Or.inl (cclass_of_compact_lifts hlift hfull)
  · exact Or.inr ⟨I,J,hd,cclass_of_compact_lifts hlift hI,cclass_of_compact_lifts hlift hJ⟩

end ModifiedCartan
