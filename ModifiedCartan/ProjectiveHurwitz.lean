import ModifiedCartan.ProjectiveConvergence

noncomputable section
set_option autoImplicit false
open Set Topology Filter Metric
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

theorem projective_limit_zero_set_open {p : ℕ}
    {F : ℕ → ℂ → ℙ ℂ (Fin p → ℂ)} {G : ℂ → ℙ ℂ (Fin p → ℂ)} {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ n, ProjectiveHolomorphicOn (F n) U)
    (hunit : ∀ n z, z ∈ U → ∀ j, (F n z).rep j ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F G atTop U) (k : Fin p) :
    IsOpen {z | z ∈ U ∧ (G z).rep k = 0} := by
  have hG : ContinuousOn G U := hconv.continuousOn (Eventually.of_forall fun n => (hF n).1).frequently
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  obtain ⟨l, hl⟩ : ∃ l, (G z).rep l ≠ 0 := by
    by_contra hh
    push Not at hh
    exact (G z).rep_nonzero (funext hh)
  have hV := hG.isOpen_inter_preimage hU (projectiveChartSet_isOpen l)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds ⟨hz.1, hl⟩)
  have hrU : ball z r ⊆ U := fun w hw => (hrV hw).1
  have hGc := hG.mono hrU
  have hlim := projective_convergence_coordinates hGc (hconv.mono hrU) l k
    (fun n w hw => hunit n w (hrU hw) l) (fun w hw => (hrV hw).2)
  have hunits : ∀ n, IsHolomorphicUnit
      (fun w => normalizeCoordinates l (F n w).rep k) (ball z r) := by
    intro n
    exact projective_unit_coordinate (projectiveHolomorphicOn_mono (hF n) hrU)
      (fun w hw j => hunit n w (hrU hw) j) l k
  have hz0 : normalizeCoordinates l (G z).rep k = 0 := by
    simp [normalizeCoordinates, hz.2]
  have hall : ∀ w ∈ ball z r, normalizeCoordinates l (G w).rep k = 0 := by
    intro w hw
    by_contra hn
    exact (hurwitz_nonvanishing isOpen_ball (convex_ball z r).isPreconnected
      hunits ((compactConvergence_iff isOpen_ball).mpr hlim) ⟨w, hw, hn⟩ z (mem_ball_self hr)) hz0
  apply mem_of_superset (ball_mem_nhds z hr)
  intro w hw
  refine ⟨hrU hw, ?_⟩
  have hh := hall w hw
  change (G w).rep k / (G w).rep l = 0 at hh
  exact (div_eq_zero_iff).mp hh |>.resolve_right (hrV hw).2

/-- Hyperplane Hurwitz for genuine locally uniform projective limits. Each
coordinate hyperplane contains the whole limit curve or is entirely avoided. -/
theorem projective_limit_coordinate_dichotomy {p : ℕ}
    {F : ℕ → ℂ → ℙ ℂ (Fin p → ℂ)} {G : ℂ → ℙ ℂ (Fin p → ℂ)} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : ∀ n, ProjectiveHolomorphicOn (F n) U)
    (hunit : ∀ n z, z ∈ U → ∀ j, (F n z).rep j ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F G atTop U) (k : Fin p) :
    (∀ z ∈ U, (G z).rep k = 0) ∨ (∀ z ∈ U, (G z).rep k ≠ 0) := by
  classical
  by_cases hn : ∃ z ∈ U, (G z).rep k ≠ 0
  · right
    have hG : ContinuousOn G U := hconv.continuousOn (Eventually.of_forall fun n => (hF n).1).frequently
    have hopen := hG.isOpen_inter_preimage hU (projectiveChartSet_isOpen k)
    have hzero := projective_limit_zero_set_open hU hF hunit hconv k
    have hdis : Disjoint (U ∩ G ⁻¹' projectiveChartSet k) {z | z ∈ U ∧ (G z).rep k = 0} := by
      apply Set.disjoint_left.mpr
      intro z ha hb
      exact ha.2 hb.2
    have hcover : U ⊆ (U ∩ G ⁻¹' projectiveChartSet k) ∪ {z | z ∈ U ∧ (G z).rep k = 0} := by
      intro z hz
      by_cases hk : (G z).rep k = 0
      · exact Or.inr ⟨hz, hk⟩
      · exact Or.inl ⟨hz, hk⟩
    obtain ⟨z, hz, hzk⟩ := hn
    have hs := hconn.subset_left_of_subset_union hopen hzero hdis hcover ⟨z, hz, hz, hzk⟩
    exact fun w hw => (hs hw).2
  · left
    push Not at hn
    exact hn

/-- The denominator for all limiting affine coordinates is selected from a
single point and is proved nonzero on the entire connected domain. -/
theorem projective_limit_global_chart {p : ℕ}
    {F : ℕ → ℂ → ℙ ℂ (Fin p → ℂ)} {G : ℂ → ℙ ℂ (Fin p → ℂ)} {U : Set ℂ}
    (hne : U.Nonempty) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : ∀ n, ProjectiveHolomorphicOn (F n) U)
    (hunit : ∀ n z, z ∈ U → ∀ j, (F n z).rep j ≠ 0)
    (hconv : TendstoLocallyUniformlyOn F G atTop U) :
    ∃ k : Fin p, (∀ z ∈ U, (G z).rep k ≠ 0) ∧
      ∀ j, CompactConvergence (fun n z => normalizeCoordinates k (F n z).rep j)
        (fun z => normalizeCoordinates k (G z).rep j) U := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨k, hk⟩ : ∃ k, (G z).rep k ≠ 0 := by
    by_contra hh
    push Not at hh
    exact (G z).rep_nonzero (funext hh)
  have hn := (projective_limit_coordinate_dichotomy hU hconn hF hunit hconv k).resolve_left
    (fun hh => hk (hh z hz))
  refine ⟨k, hn, fun j => (compactConvergence_iff hU).mpr ?_⟩
  exact projective_convergence_coordinates
    (hconv.continuousOn (Eventually.of_forall fun n => (hF n).1).frequently) hconv k j
    (fun n w hw => hunit n w hw k) hn

end ModifiedCartan
