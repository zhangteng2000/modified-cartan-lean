import ModifiedCartan.Extraction
import ModifiedCartan.Rescaling

noncomputable section
set_option autoImplicit false
open Filter Topology Set
namespace ModifiedCartan

/-- A common subsequence and actual points witnessing quadratic escape. -/
theorem finite_escape_points {ι : Type*} [Fintype ι]
    {g : ι → ℕ → ℂ → ℂ} {U : Set ℂ}
    (hc : ∀ i n, ContinuousOn (g i n) U) (he : ∀ i, EscapesOnCompact (g i) U) :
    ∃ K : ι → Set ℂ, (∀ i, K i ⊆ U ∧ IsCompact (K i)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ point : ι → ℕ → ℂ,
        ∀ i n, point i n ∈ K i ∧ ((n : ℝ) + 1) ^ 2 ≤ ‖g i (φ n) (point i n)‖ := by
  classical
  choose K hKU hK hne hlim using he
  have hbounds : ∀ n : ℕ, ∀ᶠ k in atTop, ∀ i,
      ((n : ℝ) + 1) ^ 2 ≤ compactSupNorm (g i k) (K i) := by
    intro n
    rw [eventually_all]
    intro i
    exact (hlim i).eventually (eventually_ge_atTop _)
  obtain ⟨φ, hφ, hbound⟩ := extraction_forall_of_eventually hbounds
  have hp : ∀ i n, ∃ z ∈ K i, compactSupNorm (g i (φ n)) (K i) = ‖g i (φ n) z‖ := by
    intro i n
    obtain ⟨z, hz, hmax⟩ := (hK i).exists_isMaxOn (hne i) ((hc i (φ n)).mono (hKU i)).norm
    refine ⟨z, hz, le_antisymm ?_ ?_⟩
    · exact csSup_le ((hne i).image _) (by rintro _ ⟨w, hw, rfl⟩; exact hmax hw)
    · exact le_csSup ((hK i).bddAbove_image ((hc i (φ n)).mono (hKU i)).norm)
        (mem_image_of_mem _ hz)
  choose point hpoint hvalue using hp
  exact ⟨K, fun i => ⟨hKU i, hK i⟩, φ, hφ, point,
    fun i n => ⟨hpoint i n, by rw [← hvalue i n]; exact hbound n i⟩⟩

theorem compactConvergence_div_nat {h : ℕ → ℂ → ℂ} {H : ℂ → ℂ} {U : Set ℂ}
    (hh : CompactConvergence h H U) (hc : ∀ n, ContinuousOn (h n) U) :
    CompactConvergence (fun n z => h n z / ((n : ℂ) + 1)) (fun _ => 0) U := by
  have hn : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hnC : Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hn
  have hconst : CompactConvergence (fun (n : ℕ) (_z : ℂ) => ((n : ℂ) + 1)⁻¹) (fun _ => 0) U := by
    intro K _ _
    exact hnC.tendstoUniformlyOn_const K
  have hm := compactConvergence_zero_mul hconst (compactConvergence_locallyBounded hh hc)
  simpa only [div_eq_mul_inv, mul_comm] using hm

end ModifiedCartan
