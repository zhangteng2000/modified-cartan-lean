import ModifiedCartan.ProjectiveLift
import ModifiedCartan.ProjectiveHurwitz
import ModifiedCartan.Montel
import ModifiedCartan.NormalizedParts

noncomputable section
set_option autoImplicit false
open Set Filter Topology Finset
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

def familyProjective {p : ℕ} (base : Fin p) (f : Family p) (n : ℕ) (z : ℂ) : ℙ ℂ (Fin p → ℂ) :=
  projectivePoint base (fun j => f j n z)

def projectiveHyperplane (p : ℕ) : Set (ℙ ℂ (Fin p → ℂ)) := {q | ∑ j, q.rep j = 0}

theorem projectivePoint_mem_hyperplane {p : ℕ} (base : Fin p) {x : Fin p → ℂ}
    (hx : x ≠ 0) (hs : ∑ j, x j = 0) : projectivePoint base x ∈ projectiveHyperplane p := by
  rw [projectivePoint_eq_mk base hx]
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) x hx
  change ∑ j, (Projectivization.mk ℂ x hx).rep j = 0
  rw [← hc]
  simp only [Pi.smul_apply, ← smul_sum, hs, smul_zero]

theorem projectivePoint_normalized_eq {p : ℕ} (base k : Fin p)
    {x : Fin p → ℂ} (hk : x k ≠ 0) :
    projectivePoint base (normalizeCoordinates k x) = projectivePoint base x := by
  have hx : x ≠ 0 := fun h => hk (congrFun h k)
  have hn : normalizeCoordinates k x ≠ 0 := by
    intro h
    have hh := congrFun h k
    simp [normalizeCoordinates, hk] at hh
  rw [projectivePoint_eq_mk base hn, projectivePoint_eq_mk base hx,
    projective_mk_normalizeCoordinates k hk hx]

theorem familyProjective_holomorphic {p : ℕ} (base : Fin p)
    {f : Family p} {U : Set ℂ} (hf : ∀ j n, IsHolomorphicUnit (f j n) U) (n : ℕ) :
    ProjectiveHolomorphicOn (familyProjective base f n) U :=
  projectivePoint_holomorphic base (fun j => (hf j n).1)
    (fun z hz he => (hf base n).2 z hz (congrFun he base))

theorem familyProjective_unit {p : ℕ} (base : Fin p)
    {f : Family p} {U : Set ℂ} (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    (n : ℕ) {z : ℂ} (hz : z ∈ U) (j : Fin p) : (familyProjective base f n z).rep j ≠ 0 := by
  exact (projectivePoint_coordinate_ne_zero base j
    (fun he => (hf base n).2 z hz (congrFun he base))).mpr ((hf j n).2 z hz)

theorem familyProjective_coordinate {p : ℕ} (base k j : Fin p)
    {f : Family p} {U : Set ℂ} (hf : ∀ i n, IsHolomorphicUnit (f i n) U)
    (n : ℕ) {z : ℂ} (hz : z ∈ U) :
    normalizeCoordinates k (familyProjective base f n z).rep j = f j n z / f k n z :=
  congrFun (projectivePoint_normalize base k
    (fun he => (hf base n).2 z hz (congrFun he base))) j

/-- The forward implication for one class, using an actual Montel extraction
and convergence in the true projective topology. -/
theorem cclass_univ_projective_limit {p : ℕ} (base : Fin p)
    {f : Family p} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U) (hI : IsCClass f univ U) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℙ ℂ (Fin p → ℂ),
      ProjectiveHolomorphicOn G U ∧ MapsTo G U (projectiveHyperplane p) ∧
      TendstoLocallyUniformlyOn (fun n => familyProjective base f (φ n)) G atTop U := by
  classical
  obtain ⟨k, hk, hb, hsum⟩ := hI
  obtain ⟨φ, hφ, hres⟩ := finite_montel_subsequence univ
    (fun j n z => f j n z / f k n z) hU
    (fun j _ n => (hf j n).1.div (hf k n).1 (hf k n).2) hb
  have hex := fun j => hres j (mem_univ j)
  choose g hg hlim using hex
  have hgk : ∀ z ∈ U, g k z = 1 := by
    intro z hz
    have hh := compactConvergence_pointwise (hlim k) hz
    have he : (fun n => f k (φ n) z / f k (φ n) z) = fun _ : ℕ => (1 : ℂ) := by
      funext n
      exact div_self ((hf k (φ n)).2 z hz)
    rw [he] at hh
    exact (tendsto_nhds_unique tendsto_const_nhds hh).symm
  have hgs : ∀ z ∈ U, ∑ j, g j z = 0 := by
    intro z hz
    have hh := compactConvergence_pointwise (compactConvergence_subsequence hsum hφ) hz
    have hs := tendsto_finsetSum univ (fun j _ => compactConvergence_pointwise (hlim j) hz)
    exact tendsto_nhds_unique hs hh
  have hn : ∀ z ∈ U, (fun j => g j z) ≠ 0 := by
    intro z hz he
    exact one_ne_zero ((hgk z hz).symm.trans (congrFun he k))
  refine ⟨φ, hφ, fun z => projectivePoint base (fun j => g j z),
    projectivePoint_holomorphic base hg hn,
    fun z hz => projectivePoint_mem_hyperplane base (hn z hz) (hgs z hz), ?_⟩
  have hc := projectivePoint_convergence base (fun j => (hg j).continuousOn)
    (fun j => (compactConvergence_iff hU).mp (hlim j)) hn
  apply hc.congr
  intro n z hz
  exact projectivePoint_normalized_eq base k ((hf k (φ n)).2 z hz)

/-- The reverse implication for a class. The global dominant coordinate is
proved using projective Hurwitz, rather than assumed as part of convergence. -/
theorem cclass_univ_of_projective_limit {p : ℕ} (base : Fin p)
    {f : Family p} {G : ℂ → ℙ ℂ (Fin p → ℂ)} {U : Set ℂ}
    (hne : U.Nonempty) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    (hG : MapsTo G U (projectiveHyperplane p))
    (hlim : TendstoLocallyUniformlyOn (familyProjective base f) G atTop U) :
    IsCClass f univ U := by
  obtain ⟨k, hk, hc⟩ := projective_limit_global_chart hne hU hconn
    (familyProjective_holomorphic base hf) (fun n z hz j => familyProjective_unit base hf n hz j) hlim
  have hquot : ∀ j, CompactConvergence (fun n z => f j n z / f k n z)
      (fun z => normalizeCoordinates k (G z).rep j) U := by
    intro j
    exact compactConvergence_congr (hc j) (fun n z hz => familyProjective_coordinate base k j hf n hz)
  refine ⟨k, mem_univ k, ?_, ?_⟩
  · intro j _
    exact compactConvergence_locallyBounded (hquot j)
      (fun n => ((hf j n).1.div (hf k n).1 (hf k n).2).continuousOn)
  · apply compactConvergence_zero_of_limit_zero (compactConvergence_finset_sum univ (fun j _ => hquot j))
    intro z hz
    simp only [normalizeCoordinates, ← sum_div]
    rw [show ∑ j, (G z).rep j = 0 from hG hz, zero_div]

end ModifiedCartan
