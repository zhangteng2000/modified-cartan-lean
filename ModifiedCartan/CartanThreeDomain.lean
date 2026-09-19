import ModifiedCartan.CartanThree
import ModifiedCartan.ProjectiveNormality

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

/-- The three-unit normality assertion localizes to any open plane domain. -/
theorem three_domain_kernel_equicontinuous {f : Family 3} {U : Set ℂ}
    (hU : IsOpen U) (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    (hs : ∀ n z, z ∈ U → ∑ j, f j n z = 0) :
    Equicontinuous (fun n (z : U) => projectiveKernel (familyProjective 0 f n z)) := by
  intro a
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds a.property)
  let ψ : ℂ → ℂ := fun z => (a : ℂ) + (r : ℂ) * z
  let χ : ℂ → ℂ := fun z => (z - (a : ℂ)) / (r : ℂ)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hψ : Differentiable ℂ ψ := by
    dsimp [ψ]
    fun_prop
  have hψmap : MapsTo ψ (disk 1) U := by
    intro z hz
    apply hrU
    have hzn : ‖z‖ < 1 := by simpa [disk] using hz
    have hnr : ‖(r : ℂ)‖ = r := by simp [hr.le]
    rw [mem_ball, dist_eq_norm]
    change ‖((a : ℂ) + (r : ℂ) * z) - (a : ℂ)‖ < r
    simpa only [add_sub_cancel_left, norm_mul, hnr, mul_one] using mul_lt_mul_of_pos_left hzn hr
  have hχ : Continuous χ := (continuous_id.sub continuous_const).div_const _
  have hχmap : MapsTo χ (ball (a : ℂ) r) (disk 1) := by
    intro z hz
    have hz' : ‖z - (a : ℂ)‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
    have hnr : ‖(r : ℂ)‖ = r := by simp [hr.le]
    have hnorm : ‖χ z‖ < 1 := by
      dsimp [χ]
      rw [norm_div, hnr]
      exact (div_lt_one hr).mpr hz'
    simpa [disk] using hnorm
  have hψχ : ∀ z, ψ (χ z) = z := by
    intro z
    dsimp [ψ, χ]
    field_simp
    ring
  have hloc : EquicontinuousAt (fun n z => projectiveKernel (familyProjective 0 f n z)) (a : ℂ) := by
    apply equicontinuousAt_of_local_subsequence_limits
    intro σ
    let g : Family 3 := fun j n z => f j (σ n) (ψ z)
    have hg : UnitFamily g := fun j n =>
      ⟨(hf j (σ n)).1.comp hψ.differentiableOn hψmap, fun z hz => (hf j (σ n)).2 _ (hψmap hz)⟩
    have hgs : ZeroSum g := fun n z hz => hs (σ n) _ (hψmap hz)
    obtain ⟨φ, hφ, G, hG, _, hlim⟩ := three_global_projective_limit hg hgs
    have hklim := (CompactSpace.uniformContinuous_of_continuous
      (projectiveKernel_continuous 3)).comp_tendstoLocallyUniformlyOn hlim
    have hpull := hklim.comp χ hχmap hχ.continuousOn
    refine ⟨φ, hφ, ball (a : ℂ) r, ball_mem_nhds _ hr,
      fun z => projectiveKernel (G (χ z)),
      ((projectiveKernel_continuous 3).comp_continuousOn hG).comp hχ.continuousOn hχmap, ?_⟩
    apply hpull.congr
    intro n z hz
    simp only [Function.comp_def, familyProjective, g, hψχ]
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := Metric.equicontinuousAt_iff.mp hloc ε hε
  exact ⟨δ, hδ, fun y hy n => hh y hy n⟩

/-- Cartan's three-term extraction on an arbitrary nonempty connected open
domain, needed when an induction step removes isolated zeros. -/
theorem three_domain_cclass {f : Family 3} {U : Set ℂ}
    (hne : U.Nonempty) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    (hs : ∀ n z, z ∈ U → ∑ j, f j n z = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsCClass (subsequence f φ) Finset.univ U := by
  obtain ⟨φ, hφ, G, _, hG, hlim⟩ := projective_limit_of_kernel_equicontinuous 0 hU hf hs
    (three_domain_kernel_equicontinuous hU hf hs)
  exact ⟨φ, hφ, cclass_univ_of_projective_limit 0 hne hU hconn (fun j n => hf j (φ n)) hG hlim⟩

end ModifiedCartan
