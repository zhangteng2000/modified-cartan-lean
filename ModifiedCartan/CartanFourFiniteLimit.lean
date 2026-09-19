import ModifiedCartan.CartanFourReduction
import ModifiedCartan.StrictLocalNormality

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

theorem four_kernel_equicontinuous_of_finite_ratio_limit {f : Family 4}
    (hf : UnitFamily f) (hs : ZeroSum f) {i j : Fin 4} (hij : i ≠ j) {H : ℂ → ℂ}
    (hlim : CompactConvergence (fun n z => f i n z / f j n z) H (disk 1))
    (hH : ∃ z ∈ disk 1, H z ≠ -1) :
    Equicontinuous (fun n (z : disk 1) => projectiveKernel (familyProjective 0 f n z)) := by
  intro a
  have hcont := fun n => (projectiveKernel_continuous 4).comp_continuousOn
    (familyProjective_holomorphic 0 hf n).1
  have hloc : EquicontinuousAt (fun n z => projectiveKernel (familyProjective 0 f n z)) (a : ℂ) := by
    apply equicontinuousAt_of_strict_local_subsequence_limits _ _
      (isOpen_ball.mem_nhds a.property) hcont
    intro σ hσ
    let r := (‖(a : ℂ)‖ + 1)/2
    have ha1 : ‖(a : ℂ)‖ < 1 := by simpa [disk] using a.property
    have hr : 0 < r := by dsimp [r]; positivity
    have hr1 : r < 1 := by dsimp [r]; linarith
    have har : (a : ℂ) ∈ disk r := by
      have : ‖(a : ℂ)‖ < r := by dsimp [r]; linarith
      simpa [disk] using this
    obtain ⟨φ, hφ, hc⟩ := four_class_of_finite_ratio_limit
      (unitFamily_subsequence hf σ) (zeroSum_subsequence hs σ) hij
      (compactConvergence_subsequence hlim hσ) hH hr.le hr1
    have hsub : disk r ⊆ disk 1 := ball_subset_ball hr1.le
    obtain ⟨ψ, hψ, G, hG, _, hconv⟩ := cclass_univ_projective_limit 0 isOpen_ball
      (fun k n => ⟨(hf k (σ (φ n))).1.mono hsub,
        fun z hz => (hf k (σ (φ n))).2 z (hsub hz)⟩) hc
    exact ⟨φ ∘ ψ, hφ.comp hψ, disk r, isOpen_ball.mem_nhds har,
      fun z => projectiveKernel (G z), (projectiveKernel_continuous 4).comp_continuousOn hG.1,
      (CompactSpace.uniformContinuous_of_continuous (projectiveKernel_continuous 4)).comp_tendstoLocallyUniformlyOn hconv⟩
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := Metric.equicontinuousAt_iff.mp hloc ε hε
  exact ⟨δ, hδ, fun y hy n => hh y hy n⟩

/-- The finite-limit reduction case is now proved on the entire unit disk,
using global normality rather than a fixed smaller-radius substitute. -/
theorem four_global_class_of_finite_ratio_limit {f : Family 4}
    (hf : UnitFamily f) (hs : ZeroSum f) {i j : Fin 4} (hij : i ≠ j) {H : ℂ → ℂ}
    (hlim : CompactConvergence (fun n z => f i n z / f j n z) H (disk 1))
    (hH : ∃ z ∈ disk 1, H z ≠ -1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsCClass (subsequence f φ) Finset.univ (disk 1) := by
  obtain ⟨φ, hφ, G, _, hG, hconv⟩ := projective_limit_of_kernel_equicontinuous 0 isOpen_ball hf hs
    (four_kernel_equicontinuous_of_finite_ratio_limit hf hs hij hlim hH)
  exact ⟨φ, hφ, cclass_univ_of_projective_limit 0 ⟨0, by simp [disk]⟩ isOpen_ball
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected (fun k n => hf k (φ n)) hG hconv⟩

theorem four_global_class_of_vanishing_ratio {f : Family 4}
    (hf : UnitFamily f) (hs : ZeroSum f) {i j : Fin 4} (hij : i ≠ j)
    (hlim : CompactConvergence (fun n z => f i n z / f j n z) (fun _ => 0) (disk 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsCClass (subsequence f φ) Finset.univ (disk 1) :=
  four_global_class_of_finite_ratio_limit hf hs hij hlim ⟨0, by simp [disk], by norm_num⟩

end ModifiedCartan
