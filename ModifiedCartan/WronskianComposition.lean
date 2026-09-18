import ModifiedCartan.TwoWronskian
import ModifiedCartan.ConvergenceJets

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem two_wronskian_comp {a : Fin 2 → ℂ → ℂ} {g : ℂ → ℂ} {z : ℂ}
    (ha : ∀ i, DifferentiableAt ℂ (a i) (g z)) (hg : DifferentiableAt ℂ g z) :
    wronskian (fun i w => a i (g w)) z = wronskian a (g z) * deriv g z := by
  have hder : ∀ i, deriv (fun w => a i (g w)) z = deriv (a i) (g z) * deriv g z := fun i =>
    ((ha i).hasDerivAt.comp z hg.hasDerivAt).deriv
  rw [wronskian_two, wronskian_two, hder 0, hder 1]
  ring

theorem compactConvergence_wronskian_comp_zero {a : Fin 2 → ℕ → ℂ → ℂ}
    {g : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) U) (hg : ∀ n, DifferentiableOn ℂ (g n) V)
    (hmap : ∀ n, MapsTo (g n) V U) (hlim : CompactConvergence g G V)
    (hW : CompactConvergence (fun n z => wronskian (fun i => a i n) (g n z)) 0 V) :
    CompactConvergence (fun n => wronskian (fun i z => a i n (g n z))) 0 V := by
  have hderlim := compactConvergence_deriv hV hlim hg
  have hdercont : ∀ n, ContinuousOn (deriv (g n)) V := by
    intro n
    simpa only [iteratedDeriv_one] using (iteratedDeriv_analyticOnNhd ((hg n).analyticOnNhd hV) 1).continuousOn
  have hb := compactConvergence_locallyBounded hderlim hdercont
  have hprod := compactConvergence_zero_mul hW hb
  apply compactConvergence_congr hprod
  intro n z hz
  exact (two_wronskian_comp
    (fun i => (ha i n (g n z) (hmap n hz)).differentiableAt (hU.mem_nhds (hmap n hz)))
    ((hg n z hz).differentiableAt (hV.mem_nhds hz))).symm

end ModifiedCartan
