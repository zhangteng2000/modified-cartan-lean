import ModifiedCartan.DiskAutomorphisms
import Mathlib.Analysis.Complex.Schwarz

noncomputable section
set_option autoImplicit false
open Complex Metric Set
namespace ModifiedCartan

theorem schwarz_pick_pseudodistance {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (disk 1)) (hmap : MapsTo f (disk 1) (disk 1))
    {z w : ℂ} (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    ‖diskAutomorphism (f w) (f z)‖ ≤ ‖diskAutomorphism w z‖ := by
  have hwn : ‖w‖ < 1 := by simpa [disk] using hw
  have hfwn : ‖f w‖ < 1 := by simpa [disk] using hmap hw
  let g : ℂ → ℂ := fun u => diskAutomorphism (f w) (f (diskAutomorphism w u))
  have hi : DifferentiableOn ℂ (diskAutomorphism w) (disk 1) :=
    (diskAutomorphism_analytic hwn).differentiableOn.mono ball_subset_closedBall
  have ho : DifferentiableOn ℂ (diskAutomorphism (f w)) (disk 1) :=
    (diskAutomorphism_analytic hfwn).differentiableOn.mono ball_subset_closedBall
  have hg : DifferentiableOn ℂ g (disk 1) :=
    ho.comp (hf.comp hi (fun _ hu => diskAutomorphism_mem_disk hwn hu))
      (fun _ hu => hmap (diskAutomorphism_mem_disk hwn hu))
  have hgmap : MapsTo g (disk 1) (closedBall (0 : ℂ) 1) := fun _ hu =>
    ball_subset_closedBall (diskAutomorphism_mem_disk hfwn (hmap (diskAutomorphism_mem_disk hwn hu)))
  have hg0 : g 0 = 0 := by simp [g, diskAutomorphism_zero, diskAutomorphism_self]
  have hu : ‖diskAutomorphism w z‖ < 1 := by
    simpa [disk] using diskAutomorphism_mem_disk hwn hz
  have h := Complex.norm_le_norm_of_mapsTo_ball hg hgmap hg0 hu
  simpa only [g, diskAutomorphism_involutive hwn hz] using h

theorem pseudodistance_eq_of_inverse {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (disk 1)) (hg : DifferentiableOn ℂ g (disk 1))
    (hfm : MapsTo f (disk 1) (disk 1)) (hgm : MapsTo g (disk 1) (disk 1))
    (hgf : ∀ z ∈ disk 1, g (f z) = z) {z w : ℂ} (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    ‖diskAutomorphism (f w) (f z)‖ = ‖diskAutomorphism w z‖ := by
  apply le_antisymm (schwarz_pick_pseudodistance hf hfm hz hw)
  simpa only [hgf z hz, hgf w hw] using
    schwarz_pick_pseudodistance hg hgm (hfm hz) (hfm hw)

theorem diskAutomorphism_pseudodistance {a z w : ℂ}
    (ha : ‖a‖ < 1) (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    ‖diskAutomorphism (diskAutomorphism a w) (diskAutomorphism a z)‖ =
      ‖diskAutomorphism w z‖ :=
  pseudodistance_eq_of_inverse
    ((diskAutomorphism_analytic ha).differentiableOn.mono ball_subset_closedBall)
    ((diskAutomorphism_analytic ha).differentiableOn.mono ball_subset_closedBall)
    (fun _ ht => diskAutomorphism_mem_disk ha ht) (fun _ ht => diskAutomorphism_mem_disk ha ht)
    (fun _ ht => diskAutomorphism_involutive ha ht) hz hw

theorem rotation_pseudodistance {ξ z w : ℂ} (hξ : ‖ξ‖ = 1)
    (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    ‖diskAutomorphism (ξ * w) (ξ * z)‖ = ‖diskAutomorphism w z‖ := by
  have hn : ξ ≠ 0 := by intro h; simpa [h] using hξ
  apply pseudodistance_eq_of_inverse (g := fun z => ξ⁻¹ * z)
    (by fun_prop) (by fun_prop) _ _ _ hz hw
  · intro t ht
    simpa only [disk, mem_ball, dist_zero_right, norm_mul, hξ, one_mul] using ht
  · intro t ht
    simpa only [disk, mem_ball, dist_zero_right, norm_mul, norm_inv, hξ, inv_one, one_mul] using ht
  · intro t _
    exact inv_mul_cancel_left₀ hn t

theorem hyperbolicDistance_diskAutomorphism {a z w : ℂ}
    (ha : ‖a‖ < 1) (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    hyperbolicDistance (diskAutomorphism a z) (diskAutomorphism a w) = hyperbolicDistance z w := by
  rw [hyperbolicDistance_eq_automorphism, hyperbolicDistance_eq_automorphism,
    diskAutomorphism_pseudodistance ha hz hw]

theorem hyperbolicDistance_rotation {ξ z w : ℂ} (hξ : ‖ξ‖ = 1)
    (hz : z ∈ disk 1) (hw : w ∈ disk 1) :
    hyperbolicDistance (ξ * z) (ξ * w) = hyperbolicDistance z w := by
  rw [hyperbolicDistance_eq_automorphism, hyperbolicDistance_eq_automorphism,
    rotation_pseudodistance hξ hz hw]

end ModifiedCartan
