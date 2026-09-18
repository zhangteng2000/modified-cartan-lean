import ModifiedCartan.TorusLocus

noncomputable section
set_option autoImplicit false
open Filter Topology Set
namespace ModifiedCartan

def TorusEquations.nullDirections {N : ℕ} (E : TorusEquations N) :
    Set (E.locus × (Fin N → ℂ)) := {w | kobayashiRoyden E.locus w.1.val w.2 = 0}

theorem torus_moment_continuous {N : ℕ} (E : TorusEquations N)
    (i : Fin E.count) (k : ℕ) :
    Continuous (fun w : E.locus × (Fin N → ℂ) => ∑ j,
      (E.polynomial i).orbitCoefficient w.1.val j *
        ((E.polynomial i).orbitRate w.1.val w.2 j) ^ k) := by
  have hbase : Continuous (fun w : E.locus × (Fin N → ℂ) => w.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hcoeff : ∀ j, Continuous (fun w : E.locus × (Fin N → ℂ) =>
      (E.polynomial i).orbitCoefficient w.1.val j) := by
    intro j
    apply continuous_iff_continuousAt.mpr
    intro w
    exact continuousAt_const.mul ((laurentMonomial_continuousAt
      ((E.polynomial i).exponent j) w.1.property.1).comp
        (f := fun w : E.locus × (Fin N → ℂ) => w.1.val) hbase.continuousAt)
  have hrate : ∀ j, Continuous (fun w : E.locus × (Fin N → ℂ) =>
      (E.polynomial i).orbitRate w.1.val w.2 j) := by
    intro j
    apply continuous_finsetSum
    intro l _
    exact continuous_const.mul (((continuous_apply l).comp continuous_snd).div
      ((continuous_apply l).comp hbase) (fun w => w.1.property.1 l))
  apply continuous_finsetSum
  intro j _
  exact (hcoeff j).mul ((hrate j).pow k)

/-- The zero directions are closed in the product of the locus and its ambient
tangent space; restriction to the intrinsic tangent bundle preserves closedness. -/
theorem torus_nullDirections_isClosed {N : ℕ} (E : TorusEquations N) :
    IsClosed E.nullDirections := by
  have heq : E.nullDirections = ⋂ i : Fin E.count, ⋂ k : Fin (E.terms i),
      {w : E.locus × (Fin N → ℂ) | ∑ j, (E.polynomial i).orbitCoefficient w.1.val j *
        ((E.polynomial i).orbitRate w.1.val w.2 j) ^ (k : ℕ) = 0} := by
    ext w
    simp only [TorusEquations.nullDirections, mem_ofPred_eq, mem_iInter]
    exact torus_locus_metric_zero_iff_moments E w.1.property
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro k
  exact isClosed_eq (torus_moment_continuous E i k) continuous_const

theorem torus_locus_compact_inf_pos {N : ℕ} (E : TorusEquations N)
    {K : Set ((Fin N → ℂ) × (Fin N → ℂ))} (hK : IsCompact K)
    (hKsub : ∀ w ∈ K, w.1 ∈ E.locus ∧ kobayashiRoyden E.locus w.1 w.2 ≠ 0) :
    0 < sInf ((fun w => kobayashiRoyden E.locus w.1 w.2) '' K) := by
  obtain ⟨ε, hε, hlower⟩ := torus_locus_compact_metric_lower E hK hKsub
  apply lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hε)
  apply le_sInf
  rintro _ ⟨w, hw, rfl⟩
  exact hlower w hw

end ModifiedCartan
