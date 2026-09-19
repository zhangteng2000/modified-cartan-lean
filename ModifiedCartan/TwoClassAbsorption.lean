import ModifiedCartan.CClassEnlargement
import ModifiedCartan.SharpTwoAbsorption

noncomputable section
set_option autoImplicit false
open Filter Topology Finset
namespace ModifiedCartan

/-- Once two disjoint full-disk C-classes leave a single index, the sharp
absorption theorem supplies an actual partition on every allowed open set.
No connectedness or relabelling assumption is used. -/
theorem cpartition_two_classes_one_remaining {p : ℕ} {f : Family p}
    (hf : UnitFamily f) (hs : ZeroSum f) {I J : Finset (Fin p)} {l : Fin p}
    (hI : IsCClass f I (disk 1)) (hJ : IsCClass f J (disk 1))
    (hd : Disjoint I J) (hl : l ∉ I ∪ J) (hcover : insert l (I ∪ J) = Finset.univ)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ disk 1)
    (hdiam : HasHyperbolicDiameterLE U (Real.log 3)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Nonempty (CPartition (subsequence f φ) U) := by
  classical
  obtain ⟨k, hk⟩ := hI
  obtain ⟨m, hm⟩ := hJ
  let S : Fin 2 → Finset (Fin p) := ![I, J]
  let d : Fin 2 → Fin p := ![k, m]
  have hdom : ∀ i, IsDominant f (S i) (disk 1) (d i) := by
    intro i; fin_cases i
    · exact hk
    · exact hm
  let A : Family 2 := fun i n z => f (d i) n z / f l n z
  let a : Family 2 := fun i n z => (∑ j ∈ S i, f j n z) / f l n z
  have hA : UnitFamily A := by
    intro i n
    exact ⟨(hf (d i) n).1.div (hf l n).1 (hf l n).2,
      fun z hz => div_ne_zero ((hf (d i) n).2 z hz) ((hf l n).2 z hz)⟩
  have ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1) := by
    intro i n
    exact (DifferentiableOn.fun_sum (fun j _ => (hf j n).1)).div (hf l n).1 (hf l n).2
  have hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) (fun _ => 0) (disk 1) := by
    intro i
    apply compactConvergence_congr (hdom i).2.2
    intro n z hz
    dsimp [a, A]
    rw [← sum_div]
    field_simp [(hf l n).2 z hz, (hf (d i) n).2 z hz]
  have hsumval : ∀ n z, z ∈ disk 1 → ∑ i, a i n z = (-1 : ℂ) := by
    intro n z hz
    have hsum : (∑ j ∈ I, f j n z) + (∑ j ∈ J, f j n z) + f l n z = 0 := by
      rw [← sum_union hd]
      have he : ∑ j ∈ insert l (I ∪ J), f j n z = 0 := by rw [hcover]; exact hs n z hz
      rw [sum_insert hl] at he
      linear_combination he
    simp only [Fin.sum_univ_two, a, S, Matrix.cons_val_zero, Matrix.cons_val_one,
      ← add_div]
    apply (div_eq_iff ((hf l n).2 z hz)).mpr
    linear_combination hsum
  have hsum : CompactConvergence (fun n z => ∑ i, a i n z) (fun _ => (-1 : ℂ)) (disk 1) := by
    have hh : CompactConvergence (fun (_ : ℕ) (_ : ℂ) => (-1 : ℂ)) (fun _ => (-1 : ℂ)) (disk 1) :=
      fun K _ _ => (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℂ)) atTop (𝓝 (-1))).tendstoUniformlyOn_const K
    exact compactConvergence_congr hh (fun n z hz => (hsumval n z hz).symm)
  obtain ⟨i, φ, hφ, hrecip⟩ := sharp_two_absorption hU hsub hdiam A a (fun _ => (-1 : ℂ))
    hA ha hsmall hsum ⟨0, by simp [disk], by norm_num⟩
  have hneI : l ∉ I := fun hh => hl (mem_union_left J hh)
  have hneJ : l ∉ J := fun hh => hl (mem_union_right I hh)
  have hvanish : CompactConvergence (fun n z => f l (φ n) z / f (d i) (φ n) z) (fun _ => 0) U := by
    exact compactConvergence_congr hrecip (fun n z hz => by dsimp [A]; simp only [inv_div])
  have henlarge : IsCClass (subsequence f φ) (insert l (S i)) U := by
    have hi : l ∉ S i := by fin_cases i <;> assumption
    have hdom' := dominant_subsequence (hdom i) hφ
    have hmono : IsDominant (subsequence f φ) (S i) U (d i) :=
      ⟨hdom'.1, fun j hj => locallyBounded_mono (hdom'.2.1 j hj) hsub,
        compactConvergence_mono hdom'.2.2 hsub⟩
    refine ⟨d i, dominant_insert_negligible hmono hi (fun n => ?_) hvanish⟩
    exact (((hf l (φ n)).1.div (hf (d i) (φ n)).1 (hf (d i) (φ n)).2).continuousOn).mono hsub
  refine ⟨φ, hφ, ?_⟩
  fin_cases i
  · apply cpartition_two_classes henlarge (cclass_mono (cclass_subsequence ⟨m, hm⟩ hφ) hsub)
    · exact disjoint_insert_left.mpr ⟨hneJ, hd⟩
    · simpa [S, insert_union] using hcover
  · apply cpartition_two_classes (cclass_mono (cclass_subsequence ⟨k, hk⟩ hφ) hsub) henlarge
    · exact disjoint_insert_right.mpr ⟨hneI, hd⟩
    · simpa [S, union_insert] using hcover

end ModifiedCartan
