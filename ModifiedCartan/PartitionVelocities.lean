import ModifiedCartan.PartitionRateDimension

noncomputable section
set_option autoImplicit false
open Set Finset Module
namespace ModifiedCartan

def partitionVelocitySubspace {p : ℕ} (x : Fin p → ℂ) (P : IndexPartition p) (k : Fin p) :
    Submodule ℂ (Fin p → ℂ) :=
  (partitionRateSubspace P k).map (LinearMap.mulLeft ℂ x)

theorem mem_partitionVelocitySubspace_iff {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (P : IndexPartition p) (k : Fin p) (v : Fin p → ℂ) :
    v ∈ partitionVelocitySubspace x P k ↔
      v k = 0 ∧ RatesConstantOnParts P (fun j => v j / x j) := by
  constructor
  · rintro ⟨r, hr, hrv⟩
    change x * r = v at hrv
    subst v
    have hrate : (fun j => (x * r) j / x j) = r := by
      funext j
      exact mul_div_cancel_left₀ (r j) (hx j)
    refine ⟨?_, ?_⟩
    · change x k * r k = 0
      rw [hr.1, mul_zero]
    · rw [hrate]
      exact hr.2
  · rintro ⟨hk, hr⟩
    refine ⟨fun j => v j / x j, ⟨by simp [hk], hr⟩, ?_⟩
    funext j
    change x j * (v j / x j) = v j
    exact mul_div_cancel₀ (v j) (hx j)

theorem partitionVelocitySubspace_finrank_le {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) {P : IndexPartition p} (hP : IsAdmissiblePartition x P)
    (k : Fin p) : finrank ℂ (partitionVelocitySubspace x P k) ≤ p / 2 - 1 :=
  (Submodule.finrank_map_le _ _).trans (admissible_rate_finrank_bound hx hP k)

def admissiblePartitions {p : ℕ} (x : Fin p → ℂ) : Finset (IndexPartition p) := by
  classical
  exact Finset.univ.filter (IsAdmissiblePartition x)

theorem mem_admissiblePartitions {p : ℕ} (x : Fin p → ℂ) (P : IndexPartition p) :
    P ∈ admissiblePartitions x ↔ IsAdmissiblePartition x P := by
  classical
  simp [admissiblePartitions]

theorem exponential_zero_velocity_iff_partition {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (k : Fin p) (v : Fin p → ℂ) :
    (v k = 0 ∧ ∀ z, exponentialSum x (fun j => v j / x j) z = 0) ↔
      ∃ P ∈ admissiblePartitions x, v ∈ partitionVelocitySubspace x P k := by
  rw [exponentialSum_zero_iff_admissible_partition]
  constructor
  · rintro ⟨hk, P, hP, hr⟩
    exact ⟨P, (mem_admissiblePartitions x P).mpr hP,
      (mem_partitionVelocitySubspace_iff hx P k v).mpr ⟨hk, hr⟩⟩
  · rintro ⟨P, hP, hv⟩
    obtain ⟨hk, hr⟩ := (mem_partitionVelocitySubspace_iff hx P k v).mp hv
    exact ⟨hk, P, (mem_admissiblePartitions x P).mp hP, hr⟩

theorem exponential_zero_velocity_finite_union {p : ℕ} {x : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) (k : Fin p) :
    {v : Fin p → ℂ | v k = 0 ∧ ∀ z, exponentialSum x (fun j => v j / x j) z = 0} =
      ⋃ P ∈ admissiblePartitions x, (partitionVelocitySubspace x P k : Set (Fin p → ℂ)) := by
  ext v
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop, SetLike.mem_coe]
  exact exponential_zero_velocity_iff_partition hx k v

theorem partition_velocity_sum_zero {p : ℕ} {x v : Fin p → ℂ}
    (hx : ∀ j, x j ≠ 0) {P : IndexPartition p} (hP : IsAdmissiblePartition x P)
    {k : Fin p} (hv : v ∈ partitionVelocitySubspace x P k) : ∑ j, v j = 0 := by
  have hr := ((mem_partitionVelocitySubspace_iff hx P k v).mp hv).2
  have hzero := exponentialSum_zero_of_admissible hP hr
  have h := moments_zero_of_exponentialSum_zero hzero 1
  simpa only [moment, pow_one, mul_div_cancel₀ _ (hx _)] using h

end ModifiedCartan
