import ModifiedCartan.CartanPairUnmerge
import ModifiedCartan.AnnulusTopology
import ModifiedCartan.AnnulusFilling

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- The finite-limit reduction case of the four-function Cartan theorem, on
any prescribed interior disk, with the original four indices restored. -/
theorem four_class_of_finite_ratio_limit {f : Family 4} (hf : UnitFamily f) (hs : ZeroSum f)
    {a b : Fin 4} (hab : a ≠ b) {F : ℂ → ℂ}
    (hlim : CompactConvergence (fun n z => f a n z / f b n z) F (disk 1))
    (hFne : ∃ z ∈ disk 1, F z ≠ -1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsCClass (subsequence f φ) Finset.univ (disk r) := by
  obtain ⟨α, β, hrα, hαβ, hβ1, N, hsum, hleft, hright, hback⟩ :=
    pair_merge_on_annulus hr hr1 (hf a) (hf b) hlim hFne
  let U := complexAnnulus α β
  have hα0 : 0 < α := hr.trans_lt hrα
  have hU1 : U ⊆ disk 1 := fun z hz => by simpa [disk] using hz.2.trans hβ1
  let g : Family 4 := subsequence f (fun n => N+n)
  have hg : ∀ j n, IsHolomorphicUnit (g j n) U := fun j n =>
    ⟨(hf j (N+n)).1.mono hU1, fun z hz => (hf j (N+n)).2 z (hU1 hz)⟩
  let assign := pairAssignment a b hab
  have hm := mergedFamily_pair_unit hg a b hab hsum
  have hsM : ∀ n z, z ∈ U → ∑ j, mergedFamily g assign j n z = 0 := by
    intro n z hz
    change (∑ j, ∑ i ∈ assignmentPart assign j, g i n z) = 0
    rw [assignmentPart_sum]
    exact hs (N+n) z (hU1 hz)
  obtain ⟨ψ, hψ, hclass⟩ := three_domain_cclass
    (complexAnnulus_nonempty hα0.le hαβ) (complexAnnulus_isOpen α β)
    (complexAnnulus_preconnected hα0.le) hm hsM
  have hc : IsCClass (subsequence f (fun n => N + ψ n)) Finset.univ U := by
    have hc' := cclass_unmerge_pair (fun j n => hg j (ψ n)) a b hab
      (fun n => hsum (ψ n)) (locallyBounded_subsequence hleft ψ)
      (locallyBounded_subsequence hright ψ) (locallyBounded_subsequence hback ψ) hclass
    rw [liftedIndices_univ] at hc'
    convert! hc' using 1
  let ρ := (α+β)/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hρr : r ≤ ρ := by dsimp [ρ]; linarith
  have hcircle : sphere (0 : ℂ) ρ ⊆ U := by
    intro z hz
    have hnorm : ‖z‖ = ρ := by simpa using hz
    change α < ‖z‖ ∧ ‖z‖ < β
    rw [hnorm]
    dsimp [ρ]
    constructor <;> linarith
  have hfill := cclass_fill_disk hρ hρ1 (fun j n => hf j (N+ψ n)) hcircle hc
  exact ⟨fun n => N+ψ n, fun m n hmn => Nat.add_lt_add_left (hψ hmn) N,
    cclass_mono hfill (ball_subset_ball hρr)⟩

theorem four_class_of_vanishing_ratio {f : Family 4} (hf : UnitFamily f) (hs : ZeroSum f)
    {a b : Fin 4} (hab : a ≠ b)
    (hlim : CompactConvergence (fun n z => f a n z / f b n z) (fun _ => 0) (disk 1))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsCClass (subsequence f φ) Finset.univ (disk r) :=
  four_class_of_finite_ratio_limit hf hs hab hlim ⟨0, by simp [disk], by norm_num⟩ hr hr1

end ModifiedCartan
