import ModifiedCartan.Convergence
import ModifiedCartan.Statements

noncomputable section
set_option autoImplicit false
open Filter Metric Set
namespace ModifiedCartan

theorem compactConvergence_comp {g : ℕ → ℂ → ℂ} {h f : ℂ → ℂ} {U V : Set ℂ}
    (hg : CompactConvergence g h U) (hf : ContinuousOn f V) (hmap : MapsTo f V U) :
    CompactConvergence (fun n z => g n (f z)) (fun z => h (f z)) V := by
  intro K hKV hK
  have himage : f '' K ⊆ U := by rintro _ ⟨z, hz, rfl⟩; exact hmap (hKV hz)
  have hu := (hg (f '' K) himage (hK.image_of_continuousOn (hf.mono hKV))).comp f
  exact hu.mono (fun z hz => mem_image_of_mem f hz)

theorem real_scale_mem_disk {η r : ℝ} (hη : 0 < η) {z : ℂ} :
    (η : ℂ) * z ∈ disk (η * r) ↔ z ∈ disk r := by
  simp only [disk, mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hη, mul_lt_mul_iff_right₀ hη]

theorem real_div_mem_disk {η r : ℝ} (hη : 0 < η) {z : ℂ} :
    z / (η : ℂ) ∈ disk r ↔ z ∈ disk (η * r) := by
  simp only [disk, mem_ball, dist_zero_right, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hη, div_lt_iff₀ hη]
  rw [mul_comm r η]

/-- Transport the actual absorption statement to any concentric source disk. -/
theorem absorption_rescale {m : ℕ} {ρ η : ℝ} (habs : AbsorptionAt m (disk ρ)) (hη : 0 < η)
    (A a : Family m) (s : ℂ → ℂ)
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk η))
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk η))
    (hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) (fun _ => 0) (disk η))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk η))
    (hsne : ∃ z ∈ disk η, s z ≠ 0) :
    ∃ i : Fin m, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CompactConvergence (fun n z => (A i (φ n) z)⁻¹) (fun _ => 0) (disk (η * ρ)) := by
  let f : ℂ → ℂ := fun z => (η : ℂ) * z
  have hf : Differentiable ℂ f := by dsimp [f]; fun_prop
  have hmap : MapsTo f (disk 1) (disk η) := by
    intro z hz
    simpa only [mul_one] using (real_scale_mem_disk hη).mpr hz
  let A' : Family m := fun i n z => A i n (f z)
  let a' : Family m := fun i n z => a i n (f z)
  have hA' : UnitFamily A' := fun i n =>
    ⟨(hA i n).1.comp hf.differentiableOn hmap, fun z hz => (hA i n).2 (f z) (hmap hz)⟩
  have ha' : ∀ i n, DifferentiableOn ℂ (a' i n) (disk 1) :=
    fun i n => (ha i n).comp hf.differentiableOn hmap
  have hsmall' : ∀ i, CompactConvergence (fun n z => a' i n z / A' i n z) (fun _ => 0) (disk 1) :=
    fun i => compactConvergence_comp (hsmall i) hf.continuous.continuousOn hmap
  have hsum' : CompactConvergence (fun n z => ∑ i, a' i n z) (fun z => s (f z)) (disk 1) :=
    compactConvergence_comp hsum hf.continuous.continuousOn hmap
  have hsne' : ∃ z ∈ disk 1, s (f z) ≠ 0 := by
    obtain ⟨z, hz, hnz⟩ := hsne
    refine ⟨z / (η : ℂ), (real_div_mem_disk hη).mpr (by simpa using hz), ?_⟩
    simpa [f, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hη.ne')] using hnz
  obtain ⟨i, φ, hφ, hconv⟩ := habs A' a' (fun z => s (f z)) hA' ha' hsmall' hsum' hsne'
  refine ⟨i, φ, hφ, ?_⟩
  have hdivcont : ContinuousOn (fun z : ℂ => z / (η : ℂ)) (disk (η * ρ)) := by fun_prop
  have hdivmap : MapsTo (fun z : ℂ => z / (η : ℂ)) (disk (η * ρ)) (disk ρ) :=
    fun z hz => (real_div_mem_disk hη).mpr hz
  have hh := compactConvergence_comp hconv hdivcont hdivmap
  simpa [A', f, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hη.ne')] using hh

end ModifiedCartan
