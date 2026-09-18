import ModifiedCartan.ZeroFactors
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
open scoped Convex
namespace ModifiedCartan

/-- The two-segment countable-avoidance argument from mathlib, localized to an
open convex set by choosing the intermediate point close to the midpoint. -/
theorem convex_open_sdiff_countable_joined {U S : Set ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hS : S.Countable)
    {a b : ℂ} (ha : a ∈ U \ S) (hb : b ∈ U \ S) : JoinedIn (U \ S) a b := by
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  let c := (2 : ℝ)⁻¹ • (a + b)
  let x := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by norm_num [c, x, Complex.real_smul]; ring
  have Ib : c + x = b := by norm_num [c, x, Complex.real_smul]; ring
  have hcU : c ∈ U := by simpa [c, midpoint_eq_smul_add] using hconv.midpoint_mem ha.1 hb.1
  have x_ne_zero : x ≠ 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) x_ne_zero
  have hbadB : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ S).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t => inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ S = ∅ := by simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb.2
    rw [inter_assoc, inter_comm S, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have hbadA : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ S).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t => inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ S = ∅ := by simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha.2
    rw [inter_assoc, inter_comm S, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  have hopen : IsOpen ((fun t : ℝ => c + t • y) ⁻¹' U) := hU.preimage (by fun_prop)
  have hnonempty : ((fun t : ℝ => c + t • y) ⁻¹' U).Nonempty := ⟨0, by simpa using hcU⟩
  obtain ⟨t, ht, htz⟩ := ((hbadB.union hbadA).dense_compl ℝ).exists_mem_open hopen hnonempty
  let z := c + t • y
  have hzU : z ∈ U := htz
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_nonempty_iff_eq_empty] at ht
  have hav : [a -[ℝ] z] ⊆ Sᶜ := by
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    simpa only [Ia] using ht.2
  have hbv : [b -[ℝ] z] ⊆ Sᶜ := by
    rw [subset_compl_iff_disjoint_right, disjoint_iff_inter_eq_empty]
    simpa only [Ib] using ht.1
  have JA : JoinedIn (U \ S) a z := JoinedIn.of_segment_subset
    (fun w hw => ⟨hconv.segment_subset ha.1 hzU hw, hav hw⟩)
  have JB : JoinedIn (U \ S) b z := JoinedIn.of_segment_subset
    (fun w hw => ⟨hconv.segment_subset hb.1 hzU hw, hbv hw⟩)
  exact JA.trans JB.symm

theorem convex_open_sdiff_countable_preconnected {U S : Set ℂ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hS : S.Countable) : IsPreconnected (U \ S) := by
  rcases (U \ S).eq_empty_or_nonempty with he | ⟨a, ha⟩
  · rw [he]
    exact isPreconnected_empty
  · exact (show IsPathConnected (U \ S) from
      ⟨a, ha, fun b hb => convex_open_sdiff_countable_joined hU hconv hS ha hb⟩).isConnected.isPreconnected

theorem holomorphic_zeros_finite_closedDisk {s : ℂ → ℂ}
    (hs : DifferentiableOn ℂ s (disk 1)) (hsne : ∃ z ∈ disk 1, s z ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    {z : ℂ | z ∈ closedBall 0 r ∧ s z = 0}.Finite := by
  classical
  obtain ⟨w, hw, hsw⟩ := hsne
  obtain ⟨T, m, g, _, _, hgnz, hfact⟩ := finite_zero_factorization hs hw hsw hr hr1
  apply T.finite_toSet.subset
  intro z hz
  by_contra hn
  have hpnz : (∏ t ∈ T, (z - t) ^ m t) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro he
    exact hn (he ▸ ht)
  have hsz := hfact z (closedBall_subset_ball hr1 hz.1)
  exact (mul_ne_zero hpnz (hgnz z hz.1)) (hsz.symm.trans hz.2)

theorem holomorphic_nonzero_convex_preconnected {s : ℂ → ℂ}
    (hs : DifferentiableOn ℂ s (disk 1)) (hsne : ∃ z ∈ disk 1, s z ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hUr : U ⊆ closedBall 0 r) :
    IsPreconnected {z : ℂ | z ∈ U ∧ s z ≠ 0} := by
  have hfinite := holomorphic_zeros_finite_closedDisk hs hsne hr hr1
  have he : {z : ℂ | z ∈ U ∧ s z ≠ 0} = U \ {z : ℂ | z ∈ closedBall 0 r ∧ s z = 0} := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, fun h => hz.2 h.2⟩
    · intro hz
      exact ⟨hz.1, fun h => hz.2 ⟨hUr hz.1, h⟩⟩
  rw [he]
  exact convex_open_sdiff_countable_preconnected hU hconv hfinite.countable

end ModifiedCartan
