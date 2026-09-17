import ModifiedCartan.Convergence
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Metrizable.ContinuousMap

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- Local boundedness of a holomorphic family implies equicontinuity on its open domain. -/
theorem holomorphic_equicontinuous {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hd : ∀ n, DifferentiableOn ℂ (g n) U) (hb : LocallyBounded g U) :
    Equicontinuous (fun n (z : U) => g n z) := by
  intro x
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds x.property)
  let ρ := r / 2
  have hρ : 0 < ρ := half_pos hr
  have hCU : closedBall (x : ℂ) ρ ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hrU
  obtain ⟨C, hC⟩ := hb (closedBall (x : ℂ) ρ) hCU (isCompact_closedBall ..)
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hCB : C ≤ B := by dsimp [B]; linarith [le_max_left C 0]
  have hmaps : ∀ n, MapsTo (g n) (ball (x : ℂ) ρ) (closedBall (g n x) (2 * B)) := by
    intro n z hz
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      have hzB := (hC n z (ball_subset_closedBall hz)).trans hCB
      have hxB := (hC n x (mem_closedBall_self hρ.le)).trans hCB
      linarith)
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  refine ⟨min ρ (ε * ρ / (2 * B)), lt_min hρ (by positivity), ?_⟩
  intro y hy n
  have hyr : dist (y : ℂ) x < ρ := (lt_min_iff.mp hy).1
  have hyε : dist (y : ℂ) x < ε * ρ / (2 * B) := (lt_min_iff.mp hy).2
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((hd n).mono (ball_subset_closedBall.trans hCU)) (hmaps n) (mem_ball.mpr hyr)
  have hsmall : (2 * B / ρ) * dist (y : ℂ) x < ε := by
    have hm := (lt_div_iff₀ (by positivity : 0 < 2 * B)).mp hyε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hρ).mpr
    nlinarith
  simpa only [dist_comm] using hschwarz.trans_lt hsmall

/-- Montel subsequence extraction on an arbitrary open subset of the complex plane. -/
theorem montel_subsequence {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hd : ∀ n, DifferentiableOn ℂ (g n) U) (hb : LocallyBounded g U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h U ∧ CompactConvergence (fun n => g (φ n)) h U := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let F : ℕ → C(U, ℂ) := fun n => ⟨fun z => g n z, (hd n).continuousOn.domRestrict⟩
  have heq : Equicontinuous (fun n (z : U) => g n z) := holomorphic_equicontinuous hU hd hb
  have hindex : ∀ f : range F, ∃ n, F n = f.val := fun f => f.property
  choose index hindex using hindex
  have hfamily : (fun f : range F => ((f.val : C(U, ℂ)) : U → ℂ)) =
      (fun f : range F => fun z : U => g (index f) z) := by
    funext f z
    exact (congrArg (fun a : C(U, ℂ) => a z) (hindex f)).symm
  have hrange : Equicontinuous (fun f : range F => ((f.val : C(U, ℂ)) : U → ℂ)) := by
    rw [hfamily]
    exact heq.comp index
  have hcompact : IsCompact (closure (range F)) := by
    let : T2Space (UniformOnFun U ℂ {K | IsCompact K}) := UniformOnFun.t2Space_of_covering (by
      apply eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion_of_mem (mem_singleton z) (show IsCompact ({z} : Set U) from isCompact_singleton))
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(U, ℂ) => (f : U → ℂ)) (𝔖 := {K | IsCompact K})
      (fun _ h => h) ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      exact hrange.equicontinuousOn K
    · intro K hK z hz
      obtain ⟨C, hC⟩ := hb {(z : ℂ)} (singleton_subset_iff.mpr z.property) isCompact_singleton
      refine ⟨closedBall (0 : ℂ) C, isCompact_closedBall .., ?_⟩
      rintro _ ⟨n, rfl⟩
      change g n z ∈ closedBall (0 : ℂ) C
      simpa using hC n z (mem_singleton (z : ℂ))
  obtain ⟨H, _, φ, hφ, hφlim⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let h : ℂ → ℂ := fun z => if hz : z ∈ U then H ⟨z, hz⟩ else 0
  have hlocal : TendstoLocallyUniformlyOn (fun n => g (φ n)) h atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have hH := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hφlim
    change TendstoLocallyUniformly (fun n (z : U) => g (φ n) z) (fun z => H z) atTop at hH
    have he : h ∘ ((↑) : U → ℂ) = (fun z => H z) := by
      funext z
      simp [h, z.property]
    rw [he]
    exact hH
  have hcompactlim := (compactConvergence_iff hU).mpr hlocal
  exact ⟨φ, hφ, h, compactConvergence_holomorphic hU hcompactlim (fun n => hd (φ n)), hcompactlim⟩

/-- Simultaneous Montel extraction for any finite subfamily. -/
theorem finite_montel_subsequence {ι : Type*} [Fintype ι]
    (S : Finset ι) (g : ι → ℕ → ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i ∈ S, ∀ n, DifferentiableOn ℂ (g i n) U)
    (hb : ∀ i ∈ S, LocallyBounded (g i) U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i ∈ S, ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h U ∧ CompactConvergence (fun n => g i (φ n)) h U := by
  classical
  let P : ι → (ℕ → ℕ) → Prop := fun i φ => i ∈ S → ∃ h : ℂ → ℂ,
    DifferentiableOn ℂ h U ∧ CompactConvergence (fun n => g i (φ n)) h U
  apply finite_subsequence_selection P
  · intro i φ ψ hφ hψ hP hi
    obtain ⟨h, hdh, hch⟩ := hP hi
    exact ⟨h, hdh, compactConvergence_subsequence hch hψ⟩
  · intro i φ hφ
    by_cases hi : i ∈ S
    · obtain ⟨ψ, hψ, h, hdh, hch⟩ := montel_subsequence hU (fun n => hd i hi (φ n))
        (locallyBounded_subsequence (hb i hi) φ)
      exact ⟨ψ, hψ, fun _ => ⟨h, hdh, hch⟩⟩
    · exact ⟨id, strictMono_id, fun h => False.elim (hi h)⟩

end ModifiedCartan
