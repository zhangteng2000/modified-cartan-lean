import ModifiedCartan.Convergence

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace ModifiedCartan

theorem locallyBounded_of_tail {g : ℕ → ℂ → ℂ} {U : Set ℂ} {N : ℕ}
    (hc : ∀ n, ContinuousOn (g n) U)
    (ht : LocallyBounded (fun n => g (N+n)) U) : LocallyBounded g U := by
  classical
  intro K hK hcompact
  obtain ⟨B,hB⟩ := ht K hK hcompact
  choose C hC using (fun n => hcompact.exists_bound_of_continuousOn ((hc n).mono hK))
  let A := ∑ n ∈ Finset.range N, max (C n) 0
  have hA : 0 ≤ A := Finset.sum_nonneg (fun n _ => le_max_right (C n) 0)
  refine ⟨max B 0+A,?_⟩
  intro n z hz
  by_cases hn : N ≤ n
  · have he : N+(n-N) = n := by omega
    have hb := hB (n-N) z hz
    dsimp only at hb
    rw [he] at hb
    exact hb.trans (by linarith [le_max_left B 0])
  · have hm : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hb : max (C n) 0 ≤ A := Finset.single_le_sum (fun i _ => le_max_right (C i) 0) hm
    exact (hC n z hz).trans ((le_max_left _ _).trans (hb.trans (by linarith [le_max_right B 0])))

theorem compactConvergence_of_tail {g : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ} {N : ℕ}
    (ht : CompactConvergence (fun n => g (N+n)) G U) : CompactConvergence g G U := by
  intro K hK hcompact
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp (ht K hK hcompact) ε hε)
  filter_upwards [eventually_ge_atTop (N+M)] with n hn
  have he : N+(n-N) = n := by omega
  simpa only [he] using hM (n-N) (by omega)

theorem isDominant_of_tail {p : ℕ} {f : Family p} {U : Set ℂ} {I : Finset (Fin p)}
    {k : Fin p} {N : ℕ} (hf : ∀ i n, IsHolomorphicUnit (f i n) U)
    (ht : IsDominant (subsequence f (fun n => N+n)) I U k) : IsDominant f I U k := by
  refine ⟨ht.1,?_,compactConvergence_of_tail ht.2.2⟩
  intro j hj
  exact locallyBounded_of_tail
    (fun n => ((hf j n).1.div (hf k n).1 (hf k n).2).continuousOn) (ht.2.1 j hj)

theorem cclass_of_tail {p : ℕ} {f : Family p} {U : Set ℂ} {I : Finset (Fin p)} {N : ℕ}
    (hf : ∀ i n, IsHolomorphicUnit (f i n) U)
    (ht : IsCClass (subsequence f (fun n => N+n)) I U) : IsCClass f I U := by
  obtain ⟨k,hk⟩ := ht
  exact ⟨k,isDominant_of_tail hf hk⟩

end ModifiedCartan
