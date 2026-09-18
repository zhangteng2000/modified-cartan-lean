import ModifiedCartan.AbsorptionReduction
import ModifiedCartan.AbsorptionPreparations

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- The absolute combination gap in the absorption induction. The proof
constructs minimizing vectors, a common maximal index, and the actual reduced family. -/
theorem absorption_combination_gap {m : ℕ} {ρ η : ℝ}
    (habs : AbsorptionAt m (disk ρ)) (hη : 0 < η) (hη1 : η < 1)
    (A a : Family (m + 1)) (s : ℂ → ℂ) (hA : UnitFamily A)
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) (fun _ => 0) (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    (hsne : ∃ z ∈ disk 1, s z ≠ 0)
    (hno : ∀ i, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence
      (fun n z => (A i (φ n) z)⁻¹) (fun _ => 0) (disk (η * ρ))) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n in atTop, c₀ ≤ leastCombinationNorm (fun i => a i n) η := by
  classical
  have hclosed : closedBall (0 : ℂ) η ⊆ disk 1 := closedBall_subset_ball hη1
  have hsub : disk η ⊆ disk 1 := ball_subset_closedBall.trans hclosed
  have hcont : ∀ i n, ContinuousOn (a i n) (closedBall (0 : ℂ) η) :=
    fun i n => (ha i n).continuousOn.mono hclosed
  by_contra hgap
  obtain ⟨φ, hφ, hlambda⟩ := nonnegative_sequence_zero_subsequence
    (fun n => leastCombinationNorm_nonneg (Nat.succ_pos m) hη.le (fun i => hcont i n)) hgap
  have hmins := fun n => leastCombinationNorm_attained (Nat.succ_pos m) hη.le (fun i => hcont i (φ n))
  choose c hc hcmin using hmins
  have hmaxs := fun n => unit_coefficients_have_maximum (Nat.succ_pos m) (hc n)
  choose j hjmax _hjpos _hjsq _hjcoeff using hmaxs
  obtain ⟨j₀, ψ, hψ, hfixed⟩ := finite_constant_subsequence j
  let θ := φ ∘ ψ
  have hθ : StrictMono θ := hφ.comp hψ
  let A' := subsequence A θ
  let a' := subsequence a θ
  let c' := fun n => c (ψ n)
  have hA' : ∀ i n, IsHolomorphicUnit (A' i n) (disk η) := fun i n =>
    ⟨(hA i (θ n)).1.mono hsub, fun z hz => (hA i (θ n)).2 z (hsub hz)⟩
  have ha' : ∀ i n, DifferentiableOn ℂ (a' i n) (disk η) :=
    fun i n => (ha i (θ n)).mono hsub
  have hsmall' : ∀ i, CompactConvergence (fun n z => a' i n z / A' i n z) (fun _ => 0) (disk η) :=
    fun i => compactConvergence_mono (compactConvergence_subsequence (hsmall i) hθ) hsub
  have hsum' : CompactConvergence (fun n z => ∑ i, a' i n z) s (disk η) :=
    compactConvergence_mono (compactConvergence_subsequence hsum hθ) hsub
  have hs : DifferentiableOn ℂ s (disk 1) := compactConvergence_holomorphic isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
  have hsne' := nontrivial_on_smaller_disk hs hη hη1.le hsne
  have hc' : ∀ n, coefficientNormSq (c' n) = 1 := fun n => hc (ψ n)
  have hmax' : ∀ n i, ‖c' n i‖ ≤ ‖c' n j₀‖ := by
    intro n i
    have hh := hjmax (ψ n) i
    rw [hfixed n] at hh
    exact hh
  have hcomb : CompactConvergence (fun n z => ∑ i, c' n i * a' i n z) (fun _ => 0) (disk η) := by
    apply compactConvergence_zero_of_diskSupNorm
      (fun n => continuousOn_finsetSum _ (fun i _ => (hcont i (θ n)).const_mul (c' n i)))
    have he : (fun n => diskSupNorm (fun z => ∑ i, c' n i * a' i n z) η) =
        (fun n => leastCombinationNorm (fun i => a i (φ (ψ n))) η) := by
      funext n
      exact (hcmin (ψ n)).symm
    change Tendsto (fun n => diskSupNorm (fun z => ∑ i, c' n i * a' i n z) η) atTop (𝓝 0)
    rw [he]
    exact hlambda.comp hψ.tendsto_atTop
  obtain ⟨i, _hij, χ, hχ, hconv⟩ := absorption_of_vanishing_combination habs hη A' a' s
    hA' ha' hsmall' hsum' hsne' c' hc' j₀ hmax' hcomb
  exact hno i ⟨θ ∘ χ, hθ.comp hχ, hconv⟩

end ModifiedCartan
