import ModifiedCartan.DominancePartition

noncomputable section
set_option autoImplicit false
open Filter Topology Set Finset
namespace ModifiedCartan

theorem compactConvergence_finset_sum {ι : Type*} (I : Finset ι)
    {g : ι → ℕ → ℂ → ℂ} {H : ι → ℂ → ℂ} {U : Set ℂ}
    (hg : ∀ i ∈ I, CompactConvergence (g i) (H i) U) :
    CompactConvergence (fun n z => ∑ i ∈ I, g i n z) (fun z => ∑ i ∈ I, H i z) U := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro K _ _
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)).tendstoUniformlyOn_const K
  | @insert i I hi ih =>
    have hI := ih (fun j hj => hg j (mem_insert_of_mem hj))
    intro K hKU hK
    simpa only [sum_insert hi, Pi.add_def] using ((hg i (mem_insert_self i I)) K hKU hK).add (hI K hKU hK)

def normalizedPart {p t : ℕ} (f : Family p) (assign : Fin p → Fin t)
    (rep : Fin t → Fin p) (i : Fin t) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ assignmentPart assign i, f j n z / f (rep i) n z

theorem normalizedPart_holomorphic {p t : ℕ} {f : Family p} {U : Set ℂ}
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    (assign : Fin p → Fin t) (rep : Fin t → Fin p) (i : Fin t) (n : ℕ) :
    DifferentiableOn ℂ (normalizedPart f assign rep i n) U := by
  exact DifferentiableOn.fun_sum (fun j _ => (hf j n).1.div (hf (rep i) n).1 (hf (rep i) n).2)

theorem normalizedPart_identity {p t : ℕ} {f : Family p} {U : Set ℂ}
    (hf : ∀ j n z, z ∈ U → f j n z ≠ 0)
    (assign : Fin p → Fin t) (rep : Fin t → Fin p) {n : ℕ} {z : ℂ} (hz : z ∈ U) :
    ∑ i, normalizedPart f assign rep i n z * f (rep i) n z = ∑ j, f j n z := by
  calc
    _ = ∑ i, ∑ j ∈ assignmentPart assign i, f j n z := by
      apply sum_congr rfl
      intro i _
      simp only [normalizedPart, sum_mul, div_mul_cancel₀ _ (hf (rep i) n z hz)]
    _ = _ := assignmentPart_sum assign _

theorem normalizedPart_limits {p t : ℕ} {f : Family p} {U : Set ℂ}
    (hf : ∀ j n, IsHolomorphicUnit (f j n) U)
    (assign : Fin p → Fin t) (rep : Fin t → Fin p)
    (hb : ∀ i j, j ∈ assignmentPart assign i →
      LocallyBounded (fun n z => f j n z / f (rep i) n z) U)
    (ha : ∀ i j, HolomorphicLimitOrEscape (fun n z => f j n z / f (rep i) n z) U) :
    ∃ H : Fin t → ℂ → ℂ, ∀ i,
      CompactConvergence (normalizedPart f assign rep i) (H i) U := by
  classical
  have hex : ∀ i j, j ∈ assignmentPart assign i → ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H U ∧ CompactConvergence (fun n z => f j n z / f (rep i) n z) H U := by
    intro i j hj
    exact (holomorphicLimitOrEscape_limit_iff (ha i j)
      (fun n => ((hf j n).1.div (hf (rep i) n).1 (hf (rep i) n).2).continuousOn)).mpr (hb i j hj)
  choose! H _hH hlim using hex
  refine ⟨fun i z => ∑ j ∈ assignmentPart assign i, H i j z, ?_⟩
  intro i
  exact compactConvergence_finset_sum _ (hlim i)

theorem compactConvergence_zero_of_limit_zero {g : ℕ → ℂ → ℂ} {H : ℂ → ℂ} {U : Set ℂ}
    (hg : CompactConvergence g H U) (hH : ∀ z ∈ U, H z = 0) :
    CompactConvergence g (fun _ => 0) U := by
  intro K hKU hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hg K hKU hK) ε hε] with n hn
  intro z hz
  simpa only [hH z (hKU hz)] using hn z hz

end ModifiedCartan
