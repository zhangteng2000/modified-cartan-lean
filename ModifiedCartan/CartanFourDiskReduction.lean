import ModifiedCartan.CartanFourFiniteLimit
import ModifiedCartan.PartitionCenters

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

theorem four_disk_class_of_finite_ratio_limit {f : Family 4} {L : ℝ}
    (hL : 0 < L) (hf : ∀ i n, IsHolomorphicUnit (f i n) (disk L))
    (hs : ∀ n z, z ∈ disk L → ∑ i, f i n z = 0)
    {i j : Fin 4} (hij : i ≠ j) {H : ℂ → ℂ}
    (hlim : CompactConvergence (fun n z => f i n z/f j n z) H (disk L))
    (hH : ∃ z ∈ disk L, H z ≠ -1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsCClass (subsequence f φ) Finset.univ (disk L) := by
  let ψ : ℂ → ℂ := fun z => (L : ℂ)*z
  have hψ : Differentiable ℂ ψ := by dsimp [ψ]; fun_prop
  have hmap : MapsTo ψ (disk 1) (disk L) := fun z hz => by
    simpa only [mul_one] using (real_scale_mem_disk hL).mpr hz
  let F : Family 4 := fun i n z => f i n (ψ z)
  have hFu : UnitFamily F := fun i n =>
    ⟨(hf i n).1.comp hψ.differentiableOn hmap,fun z hz => (hf i n).2 (ψ z) (hmap hz)⟩
  have hFs : ZeroSum F := fun n z hz => hs n (ψ z) (hmap hz)
  have hH' : ∃ z ∈ disk 1, H (ψ z) ≠ -1 := by
    obtain ⟨z,hz,hn⟩ := hH
    refine ⟨z/(L : ℂ),(real_div_mem_disk hL).mpr (by simpa using hz),?_⟩
    simpa [ψ,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hL.ne')] using hn
  obtain ⟨φ,hφ,hclass⟩ := four_global_class_of_finite_ratio_limit hFu hFs hij
    (compactConvergence_comp hlim hψ.continuous.continuousOn hmap) hH'
  refine ⟨φ,hφ,?_⟩
  have hback : MapsTo (fun z : ℂ => z/(L : ℂ)) (disk L) (disk 1) := fun z hz =>
    (real_div_mem_disk hL).mpr (by simpa using hz)
  apply cclass_congr (cclass_comp hclass (by fun_prop) hback)
  intro i n z _
  simp [subsequence,F,ψ,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hL.ne')]

theorem vanishing_quotient_indices_ne {p : ℕ} {f : Family p} {U : Set ℂ}
    (hU : U.Nonempty) (hf : ∀ i n, IsHolomorphicUnit (f i n) U)
    {i j : Fin p} {φ : ℕ → ℕ}
    (hlim : CompactConvergence (fun n z => f i (φ n) z/f j (φ n) z) (fun _ => 0) U) : i ≠ j := by
  intro hij
  subst j
  obtain ⟨z,hz⟩ := hU
  have h := compactConvergence_pointwise hlim hz
  have he : (fun n => f i (φ n) z/f i (φ n) z) = (fun _ : ℕ => (1 : ℂ)) :=
    funext (fun n => div_self ((hf i (φ n)).2 z hz))
  rw [he] at h
  have hh : (1 : ℂ) = 0 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at hh

end ModifiedCartan
