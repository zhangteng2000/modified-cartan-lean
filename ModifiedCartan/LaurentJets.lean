import ModifiedCartan.Laurent
import ModifiedCartan.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow

noncomputable section
set_option autoImplicit false
open Finset Set Filter Topology
namespace ModifiedCartan

theorem laurentMonomial_ne_zero {N : ℕ} (α : Fin N → ℤ) {x : Fin N → ℂ}
    (hx : ∀ j, x j ≠ 0) : laurentMonomial α x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => zpow_ne_zero _ (hx j))

theorem laurentMonomial_holomorphicUnit {N : ℕ} (α : Fin N → ℤ)
    {F : ℂ → Fin N → ℂ} {U : Set ℂ}
    (hF : ∀ j, IsHolomorphicUnit (fun z => F z j) U) :
    IsHolomorphicUnit (fun z => laurentMonomial α (F z)) U := by
  refine ⟨DifferentiableOn.fun_finsetProd (fun j _ => (hF j).1.zpow (Or.inl (hF j).2)), ?_⟩
  intro z hz
  exact laurentMonomial_ne_zero α (fun j => (hF j).2 z hz)

theorem hasDerivAt_finsetProd_logarithmic {ι : Type*} (I : Finset ι)
    {f : ι → ℂ → ℂ} {d : ι → ℂ} {x : ℂ}
    (hf : ∀ i ∈ I, HasDerivAt (f i) (d i) x) (hne : ∀ i ∈ I, f i x ≠ 0) :
    HasDerivAt (fun z => ∏ i ∈ I, f i z)
      ((∏ i ∈ I, f i x) * ∑ i ∈ I, d i / f i x) x := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hasDerivAt_const x (1 : ℂ)
  | @insert i I hi ih =>
    have hI := ih (fun j hj => hf j (mem_insert_of_mem hj))
      (fun j hj => hne j (mem_insert_of_mem hj))
    have hh := (hf i (mem_insert_self i I)).mul hI
    simp only [prod_insert hi, sum_insert hi]
    have he : (f i x * ∏ j ∈ I, f j x) * (d i / f i x + ∑ j ∈ I, d j / f j x) =
        d i * (∏ j ∈ I, f j x) + f i x * ((∏ j ∈ I, f j x) * ∑ j ∈ I, d j / f j x) := by
      field_simp [hne i (mem_insert_self i I)]
    rw [he]
    simpa only [Pi.mul_def] using hh

theorem laurentMonomial_hasDerivAt {N : ℕ} (α : Fin N → ℤ)
    {F : ℂ → Fin N → ℂ} {d : Fin N → ℂ} {x : ℂ}
    (hF : ∀ j, HasDerivAt (fun z => F z j) (d j) x)
    (hne : ∀ j, F x j ≠ 0) :
    HasDerivAt (fun z => laurentMonomial α (F z))
      (laurentMonomial α (F x) * ∑ j, (α j : ℂ) * (d j / F x j)) x := by
  classical
  have hp : ∀ j, HasDerivAt (fun z => F z j ^ α j)
      ((α j : ℂ) * (F x j) ^ (α j - 1) * d j) x := by
    intro j
    simpa only [Function.comp_def] using
      (hasDerivAt_zpow (α j) (F x j) (Or.inl (hne j))).comp x (hF j)
  have hh := hasDerivAt_finsetProd_logarithmic univ (fun j _ => hp j)
    (fun j _ => zpow_ne_zero _ (hne j))
  have he : (∑ j, (α j : ℂ) * (F x j) ^ (α j - 1) * d j / (F x j) ^ α j) =
      ∑ j, (α j : ℂ) * (d j / F x j) := by
    apply sum_congr rfl
    intro j _
    rw [zpow_sub₀ (hne j), zpow_one]
    field_simp [hne j, zpow_ne_zero (α j) (hne j)]
  rw [he] at hh
  exact hh

theorem laurentMonomial_continuousAt {N : ℕ} (α : Fin N → ℤ) {x : Fin N → ℂ}
    (hx : ∀ j, x j ≠ 0) : ContinuousAt (laurentMonomial α) x := by
  unfold laurentMonomial
  apply tendsto_finsetProd
  intro j _
  exact (continuous_apply j).continuousAt.zpow₀ (α j) (Or.inl (hx j))

theorem laurent_term_hasDerivAt_scaled {N q : ℕ} (P : LaurentData N q) (i : Fin q)
    {F : ℂ → Fin N → ℂ} {x v : Fin N → ℂ} {t : ℝ}
    (hx : ∀ j, x j ≠ 0) (hcenter : F 0 = x)
    (hder : ∀ j, HasDerivAt (fun z => F z j) ((t : ℂ) * v j) 0) :
    HasDerivAt (fun z => P.coefficient i * laurentMonomial (P.exponent i) (F z))
      ((t : ℂ) * P.orbitCoefficient x i * P.orbitRate x v i) 0 := by
  have hn : ∀ j, F 0 j ≠ 0 := by simpa only [hcenter] using hx
  have he := (laurentMonomial_hasDerivAt (P.exponent i) hder hn).const_mul (P.coefficient i)
  rw [hcenter] at he
  have hsum : (∑ j, (P.exponent i j : ℂ) * ((t : ℂ) * v j / x j)) =
      (t : ℂ) * ∑ j, (P.exponent i j : ℂ) * (v j / x j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum] at he
  have hout : (t : ℂ) * P.orbitCoefficient x i * P.orbitRate x v i =
      P.coefficient i * (laurentMonomial (P.exponent i) x *
        ((t : ℂ) * ∑ j, (P.exponent i j : ℂ) * (v j / x j))) := by
    unfold LaurentData.orbitCoefficient LaurentData.orbitRate
    ring
  rw [hout]
  exact he

theorem laurent_orbitCoefficient_tendsto {N q : ℕ} (P : LaurentData N q)
    {x : Fin N → ℂ} {xn : ℕ → Fin N → ℂ} (hx : ∀ j, x j ≠ 0)
    (hlim : Tendsto xn atTop (𝓝 x)) (i : Fin q) :
    Tendsto (fun n => P.orbitCoefficient (xn n) i) atTop (𝓝 (P.orbitCoefficient x i)) := by
  exact tendsto_const_nhds.mul ((laurentMonomial_continuousAt (P.exponent i) hx).tendsto.comp hlim)

theorem laurent_orbitRate_tendsto {N q : ℕ} (P : LaurentData N q)
    {x v : Fin N → ℂ} {xn vn : ℕ → Fin N → ℂ} (hx : ∀ j, x j ≠ 0)
    (hxlim : Tendsto xn atTop (𝓝 x)) (hvlim : Tendsto vn atTop (𝓝 v)) (i : Fin q) :
    Tendsto (fun n => P.orbitRate (xn n) (vn n) i) atTop (𝓝 (P.orbitRate x v i)) := by
  apply tendsto_finsetSum
  intro j _
  exact tendsto_const_nhds.mul
    (((continuous_apply j).tendsto v |>.comp hvlim).div
      ((continuous_apply j).tendsto x |>.comp hxlim) (hx j))

end ModifiedCartan
