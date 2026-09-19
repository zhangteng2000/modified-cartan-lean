import ModifiedCartan.CartanThreeDomain

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped LinearAlgebra.Projectivization
namespace ModifiedCartan

/-- The two-omitted-value normal-family conclusion is derived from the proved
three-unit theorem. Divergence here means reciprocal decay on every compact set. -/
theorem unit_omitting_minus_one_normal {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hg : ∀ n, IsHolomorphicUnit (g n) U)
    (homit : ∀ n z, z ∈ U → g n z ≠ -1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ CompactConvergence (fun n => g (φ n)) G U) ∨
        CompactConvergence (fun n z => (g (φ n) z)⁻¹) (fun _ => 0) U) := by
  let f : Family 3 := fun j n z => ![g n z, 1, -1 - g n z] j
  have hf : ∀ j n, IsHolomorphicUnit (f j n) U := by
    intro j n
    fin_cases j
    · exact hg n
    · exact ⟨differentiableOn_const 1, fun z _ => one_ne_zero⟩
    · refine ⟨(differentiableOn_const (-1)).sub (hg n).1, ?_⟩
      intro z hz he
      have hgz : g n z = -1 := by change -1 - g n z = 0 at he; linear_combination -he
      exact homit n z hz hgz
  have hs : ∀ n z, z ∈ U → ∑ j, f j n z = 0 := by
    intro n z _
    simp [Fin.sum_univ_three, f]
    ring
  obtain ⟨φ, hφ, G, hG, hGH, hlim⟩ := projective_limit_of_kernel_equicontinuous 0 hU hf hs
    (three_domain_kernel_equicontinuous hU hf hs)
  have hF := fun n => familyProjective_holomorphic 0 hf (φ n)
  have hunit : ∀ n z, z ∈ U → ∀ j, (familyProjective 0 f (φ n) z).rep j ≠ 0 :=
    fun n z hz j => familyProjective_unit 0 hf (φ n) hz j
  rcases projective_limit_coordinate_dichotomy hU hconn hF hunit hlim 1 with hzero | hnonzero
  · have hn0 : ∀ z ∈ U, (G z).rep 0 ≠ 0 := by
      intro z hz h0
      have hsG := hGH hz
      change ∑ j, (G z).rep j = 0 at hsG
      rw [Fin.sum_univ_three, h0, hzero z hz] at hsG
      have h2 : (G z).rep 2 = 0 := by simpa using hsG
      apply (G z).rep_nonzero
      funext j
      fin_cases j <;> simp [h0, hzero z hz, h2]
    have hcoord := projective_convergence_coordinates hG hlim 0 1
      (fun n z hz => hunit n z hz 0) hn0
    have hq : CompactConvergence (fun n z => (g (φ n) z)⁻¹)
        (fun z => normalizeCoordinates 0 (G z).rep 1) U := by
      apply compactConvergence_congr ((compactConvergence_iff hU).mpr hcoord)
      intro n z hz
      rw [familyProjective_coordinate 0 0 1 hf (φ n) hz]
      simp [f]
    exact ⟨φ, hφ, Or.inr (compactConvergence_zero_of_limit_zero hq
      (fun z hz => by simp [normalizeCoordinates, hzero z hz]))⟩
  · have hcoord := projective_convergence_coordinates hG hlim 1 0
      (fun n z hz => hunit n z hz 1) hnonzero
    have hq : CompactConvergence (fun n => g (φ n))
        (fun z => normalizeCoordinates 1 (G z).rep 0) U := by
      apply compactConvergence_congr ((compactConvergence_iff hU).mpr hcoord)
      intro n z hz
      rw [familyProjective_coordinate 0 1 0 hf (φ n) hz]
      simp [f]
    exact ⟨φ, hφ, Or.inl ⟨_, compactConvergence_holomorphic hU hq (fun n => (hg (φ n)).1), hq⟩⟩

/-- A two-omitted-value unit family has a subsequence tending to zero,
tending to infinity, or tending to an everywhere nonzero holomorphic function. -/
theorem unit_omitting_minus_one_trichotomy {g : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hg : ∀ n, IsHolomorphicUnit (g n) U)
    (homit : ∀ n z, z ∈ U → g n z ≠ -1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (CompactConvergence (fun n => g (φ n)) (fun _ => 0) U ∨
       CompactConvergence (fun n z => (g (φ n) z)⁻¹) (fun _ => 0) U ∨
       ∃ G : ℂ → ℂ, IsHolomorphicUnit G U ∧ CompactConvergence (fun n => g (φ n)) G U) := by
  obtain ⟨φ, hφ, hfinite | hinfty⟩ := unit_omitting_minus_one_normal hU hconn hg homit
  · obtain ⟨G, hG, hlim⟩ := hfinite
    by_cases hne : ∃ z ∈ U, G z ≠ 0
    · exact ⟨φ, hφ, Or.inr (Or.inr ⟨G, ⟨hG, hurwitz_nonvanishing hU hconn (fun n => hg (φ n)) hlim hne⟩, hlim⟩)⟩
    · push Not at hne
      exact ⟨φ, hφ, Or.inl (compactConvergence_zero_of_limit_zero hlim hne)⟩
  · exact ⟨φ, hφ, Or.inr (Or.inl hinfty)⟩

end ModifiedCartan
