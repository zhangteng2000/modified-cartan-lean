import ModifiedCartan.NormalizedHyperplane

noncomputable section
set_option autoImplicit false
open Set Finset Module Filter Topology
namespace ModifiedCartan

def indexPart {p : ℕ} (P : IndexPartition p) (j : Fin p) : P.parts :=
  ⟨P.part j, P.part_mem.mpr (Finset.mem_univ j)⟩

def partitionTorusParam {p : ℕ} (x : Fin p → ℂ) (P : IndexPartition p)
    (s : P.parts → ℂ) : Fin p → ℂ := fun j => s (indexPart P j) * x j

def normalizedPartitionTorus {p : ℕ} (x : Fin p → ℂ) (P : IndexPartition p) (k : Fin p) :
    Set (Fin p → ℂ) :=
  {y | ∃ s : P.parts → ℂ, (∀ I, s I ≠ 0) ∧ s (indexPart P k) = 1 ∧
    partitionTorusParam x P s = y}

theorem indexPart_eq_of_mem {p : ℕ} (P : IndexPartition p) {I : Finset (Fin p)}
    (hI : I ∈ P.parts) {j : Fin p} (hj : j ∈ I) : indexPart P j = ⟨I, hI⟩ :=
  Subtype.ext (P.part_eq_of_mem hI hj)

theorem normalizedPartitionTorus_mem_iff {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (P : IndexPartition p) (k : Fin p) (y : Fin p → ℂ) :
    y ∈ normalizedPartitionTorus x P k ↔
      (∀ j, y j ≠ 0) ∧ y k = x k ∧ RatesConstantOnParts P (fun j => y j / x j) := by
  classical
  constructor
  · rintro ⟨s, hs, hsk, rfl⟩
    refine ⟨fun j => mul_ne_zero (hs _) (hx j), ?_, ?_⟩
    · simp only [partitionTorusParam, hsk, one_mul]
    · intro I hI i hi j hj
      simp only [partitionTorusParam, indexPart_eq_of_mem P hI hi,
        indexPart_eq_of_mem P hI hj, mul_div_cancel_right₀ _ (hx _)]
  · rintro ⟨hy, hk, hr⟩
    let rep : P.parts → Fin p := fun I => Classical.choose (P.nonempty_of_mem_parts I.property)
    have hrep : ∀ I : P.parts, rep I ∈ I.val := fun I =>
      Classical.choose_spec (P.nonempty_of_mem_parts I.property)
    let s : P.parts → ℂ := fun I => y (rep I) / x (rep I)
    have hs : ∀ j, s (indexPart P j) = y j / x j := by
      intro j
      exact hr (P.part j) (P.part_mem.mpr (Finset.mem_univ j))
        (rep (indexPart P j)) (hrep _) j (P.mem_part (Finset.mem_univ j))
    refine ⟨s, fun I => div_ne_zero (hy _) (hx _), ?_, ?_⟩
    · rw [hs k, hk, div_self (hx k)]
    · funext j
      change s (indexPart P j) * x j = y j
      rw [hs j, div_mul_cancel₀ _ (hx j)]

theorem normalizedPartitionTorus_contains_base {p : ℕ} (x : Fin p → ℂ)
    (P : IndexPartition p) (k : Fin p) : x ∈ normalizedPartitionTorus x P k := by
  refine ⟨fun _ => 1, fun _ => one_ne_zero, rfl, ?_⟩
  funext j
  simp [partitionTorusParam]

theorem normalizedPartitionTorus_subset_hyperplane {p : ℕ} {x : Fin p → ℂ}
    {P : IndexPartition p} (hP : IsAdmissiblePartition x P) (k : Fin p)
    (hx : x ∈ (normalizedHyperplaneEquations k).locus) :
    normalizedPartitionTorus x P k ⊆ (normalizedHyperplaneEquations k).locus := by
  intro y hy
  obtain ⟨hyn, hyk, hyr⟩ := (normalizedPartitionTorus_mem_iff hx.1 P k y).mp hy
  apply (mem_normalizedHyperplane k y).mpr
  refine ⟨hyn, ?_, hyk.trans ((mem_normalizedHyperplane k x).mp hx).2.2⟩
  have he := exponentialSum_zero_of_admissible hP hyr
  have hm := moments_zero_of_exponentialSum_zero he 1
  simpa only [moment, pow_one, mul_div_cancel₀ _ (hx.1 _)] using hm

theorem exponentialOrbit_mem_partitionTorus {p : ℕ} {x v : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (P : IndexPartition p) (k : Fin p)
    (hv : v ∈ partitionVelocitySubspace x P k) (z : ℂ) :
    exponentialOrbit x v z ∈ normalizedPartitionTorus x P k := by
  obtain ⟨hvk, hvr⟩ := (mem_partitionVelocitySubspace_iff hx P k v).mp hv
  apply (normalizedPartitionTorus_mem_iff hx P k _).mpr
  refine ⟨fun j => exponentialOrbit_nonzero hx z j, ?_, ?_⟩
  · simp [exponentialOrbit, hvk]
  · intro I hI i hi j hj
    simp only [exponentialOrbit, mul_div_cancel_left₀ _ (hx _), hvr I hI i hi j hj]

/-- The explicit exponential curve realizes every vector in the stated
projective torus velocity space. -/
theorem partition_velocity_realized_by_entire_curve {p : ℕ} {x v : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (P : IndexPartition p) (k : Fin p)
    (hv : v ∈ partitionVelocitySubspace x P k) :
    ∃ F : ℂ → Fin p → ℂ, Differentiable ℂ F ∧ F 0 = x ∧
      (∀ j, HasDerivAt (fun z => F z j) (v j) 0) ∧
      (∀ z, F z ∈ normalizedPartitionTorus x P k) := by
  refine ⟨exponentialOrbit x v, ?_, exponentialOrbit_at_zero x v,
    exponentialOrbit_hasDerivAt hx, exponentialOrbit_mem_partitionTorus hx P k hv⟩
  intro z
  apply differentiableAt_pi.mpr
  intro j
  unfold exponentialOrbit
  fun_prop

theorem partition_torus_curve_velocity {p : ℕ} {x v : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (P : IndexPartition p) (k : Fin p)
    {F : ℂ → Fin p → ℂ}
    (hF : ∀ z ∈ disk 1, F z ∈ normalizedPartitionTorus x P k)
    (hd : ∀ j, HasDerivAt (fun z => F z j) (v j) 0) :
    v ∈ partitionVelocitySubspace x P k := by
  have h0 : (0 : ℂ) ∈ disk 1 := by simp [disk]
  apply (mem_partitionVelocitySubspace_iff hx P k v).mpr
  constructor
  · have heq : (fun z => F z k) =ᶠ[𝓝 (0 : ℂ)] (fun _ => x k) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds h0] with z hz
      exact ((normalizedPartitionTorus_mem_iff hx P k (F z)).mp (hF z hz)).2.1
    exact (hd k).unique ((hasDerivAt_const 0 (x k)).congr_of_eventuallyEq heq)
  · intro I hI i hi j hj
    have heq : (fun z => F z i / x i) =ᶠ[𝓝 (0 : ℂ)] (fun z => F z j / x j) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds h0] with z hz
      exact ((normalizedPartitionTorus_mem_iff hx P k (F z)).mp (hF z hz)).2.2 I hI i hi j hj
    exact ((hd i).div_const (x i)).unique
      (((hd j).div_const (x j)).congr_of_eventuallyEq heq)

theorem partition_torus_tangent_curve_iff {p : ℕ} {x v : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (P : IndexPartition p) (k : Fin p) :
    v ∈ partitionVelocitySubspace x P k ↔
      ∃ F : ℂ → Fin p → ℂ, DifferentiableOn ℂ F (disk 1) ∧ F 0 = x ∧
        (∀ j, HasDerivAt (fun z => F z j) (v j) 0) ∧
        (∀ z ∈ disk 1, F z ∈ normalizedPartitionTorus x P k) := by
  constructor
  · intro hv
    obtain ⟨F, hF, hcenter, hd, hmap⟩ := partition_velocity_realized_by_entire_curve hx P k hv
    exact ⟨F, hF.differentiableOn, hcenter, hd, fun z _ => hmap z⟩
  · rintro ⟨F, _, _, hd, hmap⟩
    exact partition_torus_curve_velocity hx P k hmap hd

end ModifiedCartan
