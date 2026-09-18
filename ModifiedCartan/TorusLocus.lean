import ModifiedCartan.TorusLimits
import ModifiedCartan.LargeDiscs

noncomputable section
set_option autoImplicit false
open Filter Topology Set
namespace ModifiedCartan

def complexTorus (N : ℕ) : Set (Fin N → ℂ) := {x | ∀ j, x j ≠ 0}

/-- A finite system of Laurent equations written with nonzero terms.
An equation may have no terms, and the system itself may be empty. -/
structure TorusEquations (N : ℕ) where
  count : ℕ
  terms : Fin count → ℕ
  polynomial : (i : Fin count) → LaurentData N (terms i)
  coefficient_ne_zero : ∀ i j, (polynomial i).coefficient j ≠ 0

def TorusEquations.locus {N : ℕ} (E : TorusEquations N) : Set (Fin N → ℂ) :=
  {x | x ∈ complexTorus N ∧ ∀ i, (E.polynomial i).eval x = 0}

/-- The zero-metric/orbit equivalence for the actual Laurent locus and the
ambient-coordinate disk definition. No smoothness is needed for this stronger coordinate form. -/
theorem torus_locus_metric_zero_iff {N : ℕ} (E : TorusEquations N)
    {x v : Fin N → ℂ} (hx : x ∈ E.locus) :
    kobayashiRoyden E.locus x v = 0 ↔ ∀ z : ℂ, exponentialOrbit x v z ∈ E.locus := by
  constructor
  · intro hk
    obtain ⟨t, htpos, ht, hdiscs⟩ := large_tangentDisc_sequence_of_zero hk
    let F : ∀ n, TangentDisc E.locus x v (t n) := fun n => Classical.choice (hdiscs n)
    have hF : ∀ j n, IsHolomorphicUnit (fun z => (F n).map z j) (disk 1) := by
      intro j n
      exact ⟨(F n).holomorphic j, fun z hz => ((F n).mapsTo z hz).1 j⟩
    have hzero : ∀ i z, (E.polynomial i).eval (exponentialOrbit x v z) = 0 := by
      intro i
      exact laurent_orbit_zero_of_large_discs (E.polynomial i) (E.coefficient_ne_zero i)
        (fun n => (F n).map) (fun _ => x) (fun _ => v) t x v hx.1
        tendsto_const_nhds tendsto_const_nhds ht htpos hF (fun n => (F n).center)
        (fun j n => (F n).tangent j) (fun n z hz => ((F n).mapsTo z hz).2 i)
    intro z
    refine ⟨?_, fun i => hzero i z⟩
    intro j
    exact mul_ne_zero (hx.1 j) (Complex.exp_ne_zero _)
  · exact kobayashiRoyden_zero_of_orbit hx.1

/-- Finite moment equations characterize zero directions for the actual locus. -/
theorem torus_locus_metric_zero_iff_moments {N : ℕ} (E : TorusEquations N)
    {x v : Fin N → ℂ} (hx : x ∈ E.locus) :
    kobayashiRoyden E.locus x v = 0 ↔
      ∀ i (k : Fin (E.terms i)), ∑ j, (E.polynomial i).orbitCoefficient x j *
        ((E.polynomial i).orbitRate x v j) ^ (k : ℕ) = 0 := by
  rw [torus_locus_metric_zero_iff E hx]
  constructor
  · intro h i
    exact (laurent_orbit_zero_iff_finite_equations (E.polynomial i) x v).mp
      (fun z => (h z).2 i)
  · intro h z
    refine ⟨fun j => mul_ne_zero (hx.1 j) (Complex.exp_ne_zero _), ?_⟩
    intro i
    exact (laurent_orbit_zero_iff_finite_equations (E.polynomial i) x v).mpr (h i) z

/-- Limiting discs with varying centers give the explicit entire orbit in the locus. -/
theorem torus_locus_orbit_of_large_discs {N : ℕ} (E : TorusEquations N)
    {x v : Fin N → ℂ} (hx : x ∈ E.locus)
    {xn vn : ℕ → Fin N → ℂ} {t : ℕ → ℝ}
    (hxlim : Tendsto xn atTop (𝓝 x)) (hvlim : Tendsto vn atTop (𝓝 v))
    (ht : Tendsto t atTop atTop) (htpos : ∀ n, 0 < t n)
    (F : ∀ n, TangentDisc E.locus (xn n) (vn n) (t n)) :
    ∀ z : ℂ, exponentialOrbit x v z ∈ E.locus := by
  have hF : ∀ j n, IsHolomorphicUnit (fun z => (F n).map z j) (disk 1) := by
    intro j n
    exact ⟨(F n).holomorphic j, fun z hz => ((F n).mapsTo z hz).1 j⟩
  have hzero : ∀ i z, (E.polynomial i).eval (exponentialOrbit x v z) = 0 := by
    intro i
    exact laurent_orbit_zero_of_large_discs (E.polynomial i) (E.coefficient_ne_zero i)
      (fun n => (F n).map) xn vn t x v hx.1 hxlim hvlim ht htpos hF (fun n => (F n).center)
      (fun j n => (F n).tangent j) (fun n z hz => ((F n).mapsTo z hz).2 i)
  intro z
  exact ⟨fun j => mul_ne_zero (hx.1 j) (Complex.exp_ne_zero _), fun i => hzero i z⟩

/-- Uniform positive lower bound on every compact subset of nonzero directions,
in ambient coordinates. This does not presume lower semicontinuity of the metric. -/
theorem torus_locus_compact_metric_lower {N : ℕ} (E : TorusEquations N)
    {K : Set ((Fin N → ℂ) × (Fin N → ℂ))} (hK : IsCompact K)
    (hKsub : ∀ w ∈ K, w.1 ∈ E.locus ∧ kobayashiRoyden E.locus w.1 w.2 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ K, ENNReal.ofReal ε ≤ kobayashiRoyden E.locus w.1 w.2 := by
  classical
  by_contra hn
  push Not at hn
  have he : ∀ n : ℕ, ∃ w ∈ K,
      kobayashiRoyden E.locus w.1 w.2 < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    exact hn (1 / ((n : ℝ) + 1)) (by positivity)
  choose w hw hkw using he
  have hd : ∀ n : ℕ, ∃ t : ℝ, (n : ℝ) + 1 < t ∧
      Nonempty (TangentDisc E.locus (w n).1 (w n).2 t) := fun n =>
    exists_large_tangentDisc_of_metric_lt (by positivity) (hkw n)
  choose t ht hdiscs using hd
  let F : ∀ n, TangentDisc E.locus (w n).1 (w n).2 (t n) := fun n => Classical.choice (hdiscs n)
  have htpos : ∀ n, 0 < t n := fun n => lt_trans (by positivity) (ht n)
  have htlim : Tendsto t atTop atTop := tendsto_atTop_mono (fun n => (ht n).le)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  obtain ⟨w₀, hw₀, φ, hφ, hwlim⟩ := hK.tendsto_subseq hw
  have horbit := torus_locus_orbit_of_large_discs E (hKsub w₀ hw₀).1
    (continuous_fst.tendsto w₀ |>.comp hwlim) (continuous_snd.tendsto w₀ |>.comp hwlim)
    (htlim.comp hφ.tendsto_atTop) (fun n => htpos (φ n)) (fun n => F (φ n))
  exact (hKsub w₀ hw₀).2 ((torus_locus_metric_zero_iff E (hKsub w₀ hw₀).1).mpr horbit)

end ModifiedCartan
