import ModifiedCartan.CauchyBounds
import ModifiedCartan.WronskianAlgebra

noncomputable section
set_option autoImplicit false
open Filter Topology
namespace ModifiedCartan

/-- Differentiate one row of a holomorphic jet relation. -/
theorem jet_relation_derivative {m k : ℕ} {g : Fin m → ℂ → ℂ} {h : ℂ → ℂ}
    {d : Fin m → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ∀ j, AnalyticOnNhd ℂ (g j) U) (hh : AnalyticOnNhd ℂ h U)
    (hd : ∀ j, DifferentiableOn ℂ (d j) U)
    (hrel : ∀ z ∈ U, ∑ j, iteratedDeriv k (g j) z * d j z = iteratedDeriv k h z)
    {z : ℂ} (hz : z ∈ U) :
    (∑ j, iteratedDeriv k (g j) z * deriv (d j) z) = iteratedDeriv (k + 1) h z -
      ∑ j, iteratedDeriv (k + 1) (g j) z * d j z := by
  have hgD : ∀ j, HasDerivAt (iteratedDeriv k (g j)) (iteratedDeriv (k + 1) (g j) z) z := by
    intro j
    rw [iteratedDeriv_succ]
    exact (iteratedDeriv_analyticOnNhd (hg j) k z hz).differentiableAt.hasDerivAt
  have hhD : HasDerivAt (iteratedDeriv k h) (iteratedDeriv (k + 1) h z) z := by
    rw [iteratedDeriv_succ]
    exact (iteratedDeriv_analyticOnNhd hh k z hz).differentiableAt.hasDerivAt
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hgD j).mul ((hd j).differentiableAt (hU.mem_nhds hz)).hasDerivAt)
  have he : (iteratedDeriv k h) =ᶠ[𝓝 z] (fun w => ∑ j, iteratedDeriv k (g j) w * d j w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hrel w hw).symm
  have heq := (hsum.congr_of_eventuallyEq he).unique hhD
  rw [Finset.sum_add_distrib] at heq
  linear_combination heq

/-- Differentiating Yd=v leaves only the last row, whose value is W/V. -/
theorem wronskian_coefficient_derivative_system {n : ℕ}
    {g : Fin (n + 2) → ℂ → ℂ} {d : Fin (n + 1) → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : ∀ j, AnalyticOnNhd ℂ (g j) U)
    (hd : ∀ j, DifferentiableOn ℂ (d j) U)
    (hrel : ∀ i : Fin (n + 1), ∀ z ∈ U,
      ∑ j, iteratedDeriv (i : ℕ) (g j.castSucc) z * d j z =
        iteratedDeriv (i : ℕ) (g (Fin.last (n + 1))) z)
    {z : ℂ} (hz : z ∈ U)
    (hV : wronskian (fun j : Fin (n + 1) => g j.castSucc) z ≠ 0) :
    ∀ i : Fin (n + 1),
      (∑ j, iteratedDeriv (i : ℕ) (g j.castSucc) z * deriv (d j) z) =
        if i = Fin.last n then wronskian g z / wronskian (fun j : Fin (n + 1) => g j.castSucc) z else 0 := by
  intro i
  rw [jet_relation_derivative hU (fun j => hg j.castSucc) (hg (Fin.last (n + 1))) hd (hrel i) hz]
  split_ifs with hi
  · subst i
    simp only [Fin.val_last]
    have hw := wronskian_last_column_residual g z (fun j => d j z) (fun i => hrel i z hz)
    rw [hw, mul_div_cancel_right₀ _ hV]
  · have hi' : (i : ℕ) < n := by
      have hne : (i : ℕ) ≠ n := by intro he; apply hi; exact Fin.ext he
      omega
    let j : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩
    have hj := hrel j z hz
    change (∑ l, iteratedDeriv ((i : ℕ) + 1) (g l.castSucc) z * d l z) =
      iteratedDeriv ((i : ℕ) + 1) (g (Fin.last (n + 1))) z at hj
    rw [hj, sub_self]

end ModifiedCartan
