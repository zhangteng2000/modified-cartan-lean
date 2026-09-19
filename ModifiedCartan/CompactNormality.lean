import ModifiedCartan.LocalNormality
import ModifiedCartan.Montel

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

/-- Equicontinuity and a compact range give genuine local uniform subsequence
convergence on any open subset of the plane. -/
theorem equicontinuous_compact_range_subsequence {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [Inhabited Y]
    {U : Set ℂ} (hU : IsOpen U) (F : ℕ → ℂ → Y)
    (hF : ∀ n, ContinuousOn (F n) U)
    (heq : Equicontinuous (fun n (z : U) => F n z))
    {S : Set Y} (hS : IsCompact S) (hFS : ∀ n, MapsTo (F n) U S) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → Y,
      ContinuousOn G U ∧ MapsTo G U S ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) G atTop U := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let f : ℕ → C(U, Y) := fun n => ⟨fun z => F n z, (hF n).domRestrict⟩
  have hindex : ∀ g : range f, ∃ n, f n = g.val := fun g => g.property
  choose index hindex using hindex
  have hrange : Equicontinuous (fun g : range f => ((g.val : C(U, Y)) : U → Y)) := by
    have he : (fun g : range f => ((g.val : C(U, Y)) : U → Y)) =
        (fun g : range f => fun z : U => F (index g) z) := by
      funext g z
      exact (congrArg (fun a : C(U, Y) => a z) (hindex g)).symm
    rw [he]
    exact heq.comp index
  have hcompact : IsCompact (closure (range f)) := by
    let : T2Space (UniformOnFun U Y {K | IsCompact K}) := UniformOnFun.t2Space_of_covering (by
      apply eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion_of_mem (mem_singleton z) (show IsCompact ({z} : Set U) from isCompact_singleton))
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(U, Y) => (g : U → Y)) (𝔖 := {K | IsCompact K})
      (fun _ h => h) ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      exact hrange.equicontinuousOn K
    · intro K hK z hz
      refine ⟨S, hS, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hFS n z.property
  obtain ⟨H, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let G : ℂ → Y := fun z => if hz : z ∈ U then H ⟨z, hz⟩ else default
  have hlocal : TendstoLocallyUniformlyOn (fun n => F (φ n)) G atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have hh := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
    change TendstoLocallyUniformly (fun n (z : U) => F (φ n) z) (fun z => H z) atTop at hh
    have he : G ∘ ((↑) : U → ℂ) = (fun z => H z) := by
      funext z
      simp [G, z.property]
    rw [he]
    exact hh
  refine ⟨φ, hφ, G, hlocal.continuousOn (Eventually.of_forall fun n => hF (φ n)).frequently, ?_, hlocal⟩
  intro z hz
  exact hS.isClosed.mem_of_tendsto (hlocal.tendsto_at hz)
    (Eventually.of_forall fun n => hFS (φ n) hz)

end ModifiedCartan
