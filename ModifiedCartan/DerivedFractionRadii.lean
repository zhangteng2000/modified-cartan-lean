import ModifiedCartan.RadialMeasureDichotomy
import ModifiedCartan.WronskianPermutations

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

def radialLargeValueSet (F : ℂ → ℂ) (b c : ℝ) : Set ℝ :=
  {r | r ∈ Icc b c ∧ ∃ z : ℂ, ‖z‖ = r ∧ 1 < ‖F z‖}

def radialCommonGoodSet {ι : Type*} (F : ι → ℂ → ℂ) (b c : ℝ) : Set ℝ :=
  {r | r ∈ Icc b c ∧ ∀ i z, ‖z‖ = r → ‖F i z‖ ≤ 1}

theorem radialCommonGoodSet_eq_complement {ι : Type*} (F : ι → ℂ → ℂ) (b c : ℝ) :
    radialCommonGoodSet F b c = Icc b c \ ⋃ i, radialLargeValueSet (F i) b c := by
  classical
  ext r
  simp only [radialCommonGoodSet,radialLargeValueSet,mem_setOf_eq,mem_diff,mem_iUnion]
  constructor
  · rintro ⟨hr,hgood⟩
    refine ⟨hr,?_⟩
    rintro ⟨i,_,z,hz,hbad⟩
    exact (not_lt_of_ge (hgood i z hz)) hbad
  · rintro ⟨hr,hbad⟩
    refine ⟨hr,fun i z hz => le_of_not_gt (fun hh => hbad ⟨i,hr,z,hz,hh⟩)⟩

theorem exists_large_orientation {ι : Type*} [Fintype ι] (F : ι → ℂ → ℂ) {b c : ℝ}
    (hbc : b < c)
    (hgood : volume (radialCommonGoodSet F b c) ≤ ENNReal.ofReal ((c-b)/2)) :
    ∃ i, ENNReal.ofReal ((c-b)/(2*((Fintype.card ι : ℝ)+1))) <
      volume (radialLargeValueSet (F i) b c) := by
  apply exists_large_component_on_interval (fun i => radialLargeValueSet (F i) b c) hbc
  simpa only [← radialCommonGoodSet_eq_complement] using hgood

def thirdDerivedFraction (g : Fin 3 → ℂ → ℂ) (z : ℂ) : ℂ :=
  g 0 z*wronskian g z/(wronskian ![g 0,g 1] z*wronskian ![g 0,g 2] z)

def fourthDerivedFraction (g : Fin 4 → ℂ → ℂ) (z : ℂ) : ℂ :=
  wronskian ![g 0,g 1] z*wronskian g z/
    (wronskian ![g 0,g 1,g 2] z*wronskian ![g 0,g 1,g 3] z)

theorem fin_three_pair_orientation (i j : Fin 3) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 1 = i ∧ σ 2 = j := by
  have h : ∀ i j : Fin 3, i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ 1 = i ∧ σ 2 = j := by decide
  exact h i j hij

theorem fin_four_pair_orientation (i j : Fin 4) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 2 = i ∧ σ 3 = j := by
  have h : ∀ i j : Fin 4, i ≠ j → ∃ σ : Equiv.Perm (Fin 4), σ 2 = i ∧ σ 3 = j := by decide
  exact h i j hij

theorem radialGood_third_pairs {g : Fin 3 → ℂ → ℂ} {b c r : ℝ}
    (hr : r ∈ radialCommonGoodSet (fun σ : Equiv.Perm (Fin 3) => thirdDerivedFraction (g ∘ σ)) b c) :
    ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧
      ∀ z ∈ sphere (0 : ℂ) r,
        ‖g k z*wronskian ![g k,g i,g j] z/(wronskian ![g k,g i] z*wronskian ![g k,g j] z)‖ ≤ 1 := by
  intro i j hij
  obtain ⟨σ,h1,h2⟩ := fin_three_pair_orientation i j hij
  refine ⟨σ 0,?_,?_,?_⟩
  · rw [← h1]
    exact σ.injective.ne (by decide)
  · rw [← h2]
    exact σ.injective.ne (by decide)
  · intro z hz
    have he : g ∘ σ = ![g (σ 0),g i,g j] := by
      funext k
      fin_cases k <;> simp [Function.comp_def,h1,h2]
    have hh := hr.2 σ z (by simpa using hz)
    simpa [thirdDerivedFraction,he,h1,h2] using hh

theorem radialGood_fourth_pairs {g : Fin 4 → ℂ → ℂ} {b c r : ℝ}
    (hr : r ∈ radialCommonGoodSet (fun σ : Equiv.Perm (Fin 4) => fourthDerivedFraction (g ∘ σ)) b c) :
    ∀ i j : Fin 4, i ≠ j → ∃ k l : Fin 4,
      k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
      ∀ z ∈ sphere (0 : ℂ) r,
        ‖wronskian ![g k,g l] z*wronskian ![g k,g l,g i,g j] z/
          (wronskian ![g k,g l,g i] z*wronskian ![g k,g l,g j] z)‖ ≤ 1 := by
  intro i j hij
  obtain ⟨σ,h2,h3⟩ := fin_four_pair_orientation i j hij
  refine ⟨σ 0,σ 1,σ.injective.ne (by decide),?_,?_,?_,?_,?_⟩
  · rw [← h2]
    exact σ.injective.ne (by decide)
  · rw [← h3]
    exact σ.injective.ne (by decide)
  · rw [← h2]
    exact σ.injective.ne (by decide)
  · rw [← h3]
    exact σ.injective.ne (by decide)
  · intro z hz
    have he : g ∘ σ = ![g (σ 0),g (σ 1),g i,g j] := by
      funext k
      fin_cases k <;> simp [Function.comp_def,h2,h3]
    have hh := hr.2 σ z (by simpa using hz)
    simpa [fourthDerivedFraction,he,h2,h3] using hh

end ModifiedCartan
