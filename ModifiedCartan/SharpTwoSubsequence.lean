import ModifiedCartan.SharpTwoSetup

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- Retain the already constructed failure points and radii when passing to a
subsequence. Every analytic and geometric property is preserved. -/
def sharpTwoSetupSubsequence {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ} {Ω : Set ℂ}
    (D : SharpTwoSetup A a s Ω) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    SharpTwoSetup (fun i n => A i (φ n)) (fun i n => a i (φ n)) s Ω where
  L := D.L
  compact := D.compact
  nonempty := D.nonempty
  subset := D.subset
  nonzero := D.nonzero
  r := D.r
  α := D.α
  β := D.β
  v := D.v
  q := D.q
  C₀ := D.C₀
  ell := D.ell
  c := D.c
  r_pos := D.r_pos
  r_lt := D.r_lt
  α_lt := D.α_lt
  β_lt := D.β_lt
  v_lt := D.v_lt
  q_pos := D.q_pos
  q_lt := D.q_lt
  C₀_nonneg := D.C₀_nonneg
  ell_pos := D.ell_pos
  c_pos := D.c_pos
  contained := D.contained
  point := fun i n => D.point i (φ n)
  point_mem := fun i n => D.point_mem i (φ n)
  ρ := fun n => D.ρ (φ n)
  radius := fun n => D.radius (φ n)
  pseudodistance := D.pseudodistance
  failure := hφ.tendsto_atTop.eventually D.failure
  endpoint_zero := D.endpoint_zero.comp hφ.tendsto_atTop
  endpoint_one := D.endpoint_one.comp hφ.tendsto_atTop
  interior_norms := hφ.tendsto_atTop.eventually D.interior_norms
  lower_sum := hφ.tendsto_atTop.eventually D.lower_sum
  growth := D.growth.comp hφ.tendsto_atTop
  controlled := hφ.tendsto_atTop.eventually D.controlled

theorem sharpTwoSetupSubsequence_point {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ} {Ω : Set ℂ}
    (D : SharpTwoSetup A a s Ω) {φ : ℕ → ℕ} (hφ : StrictMono φ) (i : Fin 2) (n : ℕ) :
    (sharpTwoSetupSubsequence D hφ).point i n = D.point i (φ n) := rfl

theorem sharpTwoSetupSubsequence_radius {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ} {Ω : Set ℂ}
    (D : SharpTwoSetup A a s Ω) {φ : ℕ → ℕ} (hφ : StrictMono φ) (n : ℕ) :
    (sharpTwoSetupSubsequence D hφ).ρ n = D.ρ (φ n) := rfl

end ModifiedCartan
