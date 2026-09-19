import ModifiedCartan.TorusLocus
import ModifiedCartan.PartitionVelocities

noncomputable section
set_option autoImplicit false
open Set Finset Module
namespace ModifiedCartan

def coordinateSumLaurent (p : ℕ) : LaurentData p p where
  coefficient _ := 1
  exponent i j := if j = i then 1 else 0

def coordinateOneLaurent {p : ℕ} (k : Fin p) : LaurentData p 2 where
  coefficient i := if i = 0 then 1 else -1
  exponent i j := if i = 0 then if j = k then 1 else 0 else 0

theorem coordinateSumLaurent_eval {p : ℕ} (x : Fin p → ℂ) :
    (coordinateSumLaurent p).eval x = ∑ j, x j := by
  classical
  simp [LaurentData.eval, coordinateSumLaurent, laurentMonomial]

theorem coordinateOneLaurent_eval {p : ℕ} (k : Fin p) (x : Fin p → ℂ) :
    (coordinateOneLaurent k).eval x = x k - 1 := by
  classical
  simp [LaurentData.eval, coordinateOneLaurent, laurentMonomial, Fin.sum_univ_two,
    sub_eq_add_neg]

/-- The global affine model of X_p obtained by setting the k-th homogeneous
coordinate to one, retaining all p coordinates and their exact zero-sum equation. -/
def normalizedHyperplaneEquations {p : ℕ} (k : Fin p) : TorusEquations p where
  count := 2
  terms := Fin.cases p (fun _ => 2)
  polynomial := Fin.cases (coordinateSumLaurent p) (fun _ => coordinateOneLaurent k)
  coefficient_ne_zero := by
    intro i j
    fin_cases i
    · change (1 : ℂ) ≠ 0
      exact one_ne_zero
    · have H : ∀ l : Fin 2, (coordinateOneLaurent k).coefficient l ≠ 0 := by
        intro l
        dsimp [coordinateOneLaurent]
        split_ifs <;> norm_num
      exact H j

theorem mem_normalizedHyperplane {p : ℕ} (k : Fin p) (x : Fin p → ℂ) :
    x ∈ (normalizedHyperplaneEquations k).locus ↔
      (∀ j, x j ≠ 0) ∧ (∑ j, x j = 0) ∧ x k = 1 := by
  change (∀ j, x j ≠ 0) ∧ (∀ i : Fin 2, _) ↔ _
  simp only [Fin.forall_fin_two]
  change ((∀ j, x j ≠ 0) ∧ (coordinateSumLaurent p).eval x = 0 ∧
    (coordinateOneLaurent k).eval x = 0) ↔ _
  rw [coordinateSumLaurent_eval, coordinateOneLaurent_eval, sub_eq_zero]

theorem normalizedHyperplane_metric_zero_iff {p : ℕ} (k : Fin p)
    {x v : Fin p → ℂ} (hx : x ∈ (normalizedHyperplaneEquations k).locus) :
    kobayashiRoyden (normalizedHyperplaneEquations k).locus x v = 0 ↔
      v k = 0 ∧ ∀ z, exponentialSum x (fun j => v j / x j) z = 0 := by
  have hx' := (mem_normalizedHyperplane k x).mp hx
  rw [torus_locus_metric_zero_iff _ hx]
  constructor
  · intro h
    have hk : (fun z => exponentialOrbit x v z k) = (fun _ : ℂ => 1) :=
      funext (fun z => ((mem_normalizedHyperplane k _).mp (h z)).2.2)
    have hd := exponentialOrbit_hasDerivAt (v := v) hx'.1 k
    rw [hk] at hd
    refine ⟨hd.unique (hasDerivAt_const 0 (1 : ℂ)), ?_⟩
    intro z
    exact ((mem_normalizedHyperplane k _).mp (h z)).2.1
  · rintro ⟨hk, hsum⟩ z
    apply (mem_normalizedHyperplane k _).mpr
    refine ⟨fun j => exponentialOrbit_nonzero hx'.1 z j, hsum z, ?_⟩
    simp [exponentialOrbit, hk, hx'.2.2]

theorem normalizedHyperplane_zero_finite_union {p : ℕ} (k : Fin p)
    {x : Fin p → ℂ} (hx : x ∈ (normalizedHyperplaneEquations k).locus) :
    {v : Fin p → ℂ | kobayashiRoyden (normalizedHyperplaneEquations k).locus x v = 0} =
      ⋃ P ∈ admissiblePartitions x, (partitionVelocitySubspace x P k : Set (Fin p → ℂ)) := by
  ext v
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop, SetLike.mem_coe]
  rw [normalizedHyperplane_metric_zero_iff k hx]
  exact exponential_zero_velocity_iff_partition hx.1 k v

end ModifiedCartan
