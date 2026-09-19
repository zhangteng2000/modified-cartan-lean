import ModifiedCartan.PartitionCenters

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

/-- An open surjection between plane domains has compact sets above every
compact target set. The lift need not be a continuous section. -/
theorem compact_lifts_of_open_surjection {ψ : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hopen : ∀ W ⊆ U, IsOpen W → IsOpen (ψ '' W))
    (hsurj : SurjOn ψ U V) (K : Set ℂ) (hKV : K ⊆ V) (hK : IsCompact K) :
    ∃ L : Set ℂ, L ⊆ U ∧ IsCompact L ∧ K ⊆ ψ '' L := by
  classical
  have hex : ∀ x : U, ∃ r : ℝ, 0 < r ∧ closedBall (x : ℂ) r ⊆ U := by
    intro x
    obtain ⟨r,hr,hh⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds x.property)
    exact ⟨r/2,half_pos hr,(closedBall_subset_ball (half_lt_self hr)).trans hh⟩
  choose r hr hball using hex
  let W : U → Set ℂ := fun x => ψ '' ball (x : ℂ) (r x)
  have hW (x : U) : IsOpen (W x) :=
    hopen _ (ball_subset_closedBall.trans (hball x)) isOpen_ball
  have hcover : K ⊆ ⋃ x : U, W x := by
    intro y hy
    obtain ⟨x,hx,he⟩ := hsurj (hKV hy)
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,⟨x,mem_ball_self (hr ⟨x,hx⟩),he⟩⟩
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover W hW hcover
  let L : Set ℂ := ⋃ x ∈ S, closedBall (x : ℂ) (r x)
  refine ⟨L,?_,S.isCompact_biUnion (fun x _ => isCompact_closedBall (x : ℂ) (r x)),?_⟩
  · intro z hz
    change z ∈ ⋃ x ∈ S, closedBall (x : ℂ) (r x) at hz
    simp only [mem_iUnion] at hz
    obtain ⟨x,hx,hz⟩ := hz
    exact hball x hz
  · intro y hy
    obtain ⟨x,hx⟩ := mem_iUnion.mp (hS hy)
    obtain ⟨hx,z,hz,he⟩ := mem_iUnion.mp hx
    exact ⟨z,mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hx,ball_subset_closedBall hz⟩⟩,he⟩

theorem locallyBounded_of_compact_lifts {ψ : ℂ → ℂ} {U V : Set ℂ} {g : ℕ → ℂ → ℂ}
    (hlift : ∀ K : Set ℂ, K ⊆ V → IsCompact K → ∃ L : Set ℂ, L ⊆ U ∧ IsCompact L ∧ K ⊆ ψ '' L)
    (hb : LocallyBounded (fun n z => g n (ψ z)) U) : LocallyBounded g V := by
  intro K hK hcK
  obtain ⟨L,hL,hcL,hcover⟩ := hlift K hK hcK
  obtain ⟨C,hC⟩ := hb L hL hcL
  refine ⟨C,?_⟩
  intro n z hz
  obtain ⟨w,hw,rfl⟩ := hcover hz
  exact hC n w hw

theorem compactConvergence_of_compact_lifts {ψ : ℂ → ℂ} {U V : Set ℂ}
    {g : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (hlift : ∀ K : Set ℂ, K ⊆ V → IsCompact K → ∃ L : Set ℂ, L ⊆ U ∧ IsCompact L ∧ K ⊆ ψ '' L)
    (hc : CompactConvergence (fun n z => g n (ψ z)) (fun z => G (ψ z)) U) :
    CompactConvergence g G V := by
  intro K hK hcK
  obtain ⟨L,hL,hcL,hcover⟩ := hlift K hK hcK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hc L hL hcL) ε hε] with n hn
  intro z hz
  obtain ⟨w,hw,rfl⟩ := hcover hz
  exact hn w hw

theorem cclass_of_compact_lifts {p : ℕ} {f : Family p} {I : Finset (Fin p)}
    {ψ : ℂ → ℂ} {U V : Set ℂ}
    (hlift : ∀ K : Set ℂ, K ⊆ V → IsCompact K → ∃ L : Set ℂ, L ⊆ U ∧ IsCompact L ∧ K ⊆ ψ '' L)
    (hc : IsCClass (fun i n z => f i n (ψ z)) I U) : IsCClass f I V := by
  obtain ⟨k,hk,hb,hs⟩ := hc
  exact ⟨k,hk,fun j hj => locallyBounded_of_compact_lifts hlift (hb j hj),
    compactConvergence_of_compact_lifts hlift hs⟩

end ModifiedCartan
