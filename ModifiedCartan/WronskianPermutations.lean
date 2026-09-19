import ModifiedCartan.NormalizedWronskian

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

theorem normalizedWronskian_comp_perm {m : ℕ} (g : Fin m → ℂ → ℂ)
    (σ : Equiv.Perm (Fin m)) (z : ℂ) :
    normalizedWronskian (g ∘ σ) z = ((Equiv.Perm.sign σ : ℤ) : ℂ)*normalizedWronskian g z := by
  simp only [normalizedWronskian_eq_det]
  exact Matrix.det_permute' σ (.of fun k j : Fin m => iteratedDeriv (k : ℕ) (g j) z/g j z)

theorem normalizedWronskian_norm_comp_perm {m : ℕ} (g : Fin m → ℂ → ℂ)
    (σ : Equiv.Perm (Fin m)) (z : ℂ) :
    ‖normalizedWronskian (g ∘ σ) z‖ = ‖normalizedWronskian g z‖ := by
  rw [normalizedWronskian_comp_perm,norm_mul]
  have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hsign,one_mul]

theorem normalizedWronskian_proximity_comp_perm {m : ℕ} (g : Fin m → ℂ → ℂ)
    (σ : Equiv.Perm (Fin m)) (R : ℝ) :
    proximityMean (normalizedWronskian (g ∘ σ)) R = proximityMean (normalizedWronskian g) R := by
  simp only [proximityMean,ValueDistribution.proximity_top,normalizedWronskian_norm_comp_perm]

theorem normalizedWronskian_inv_proximity_comp_perm {m : ℕ} (g : Fin m → ℂ → ℂ)
    (σ : Equiv.Perm (Fin m)) (R : ℝ) :
    proximityMean (fun z => (normalizedWronskian (g ∘ σ) z)⁻¹) R =
      proximityMean (fun z => (normalizedWronskian g z)⁻¹) R := by
  simp only [proximityMean,ValueDistribution.proximity_top,norm_inv,normalizedWronskian_norm_comp_perm]

end ModifiedCartan
