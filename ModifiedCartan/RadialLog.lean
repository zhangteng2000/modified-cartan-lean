import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Real MeasureTheory Set Filter intervalIntegral
namespace ModifiedCartan

def radialLog (u r : ℝ) : ℝ := Real.log 2 - Real.log (r - u)

theorem abs_mul_log_le_one {x : ℝ} (hx : |x| ≤ 1) : |x * Real.log x| ≤ 1 := by
  by_cases h0 : x = 0
  · simp [h0]
  have h := (Real.abs_log_mul_self_lt |x| (abs_pos.mpr h0) hx).le
  simpa [abs_mul, Real.log_abs, mul_comm] using h

theorem radialLog_integrable (u b c : ℝ) : IntervalIntegrable (radialLog u) volume b c := by
  have h : IntervalIntegrable (fun r : ℝ => Real.log (r - u)) volume b c := by
    simpa using (intervalIntegrable_log' (a := b - u) (b := c - u)).comp_sub_right u
  exact intervalIntegrable_const.sub h

theorem radialLog_integral_bound {b c u : ℝ} (hb : 0 ≤ b) (hbc : b < c)
    (hc : c ≤ 1) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ r in b..c, radialLog u r) ≤ Real.log 2 + 3 := by
  have hi : IntervalIntegrable (fun r : ℝ => Real.log (r - u)) volume b c := by
    simpa using (intervalIntegrable_log' (a := b - u) (b := c - u)).comp_sub_right u
  have hprim : (∫ r in b..c, radialLog u r) =
      (c - b) * Real.log 2 - ((c - u) * Real.log (c - u) -
        (b - u) * Real.log (b - u) - (c - u) + (b - u)) := by
    rw [show radialLog u = (fun r => Real.log 2 - Real.log (r - u)) from rfl,
      intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const, intervalIntegral.integral_comp_sub_right, integral_log]
    rfl
  rw [hprim]
  have hbabs : |b - u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcabs : |c - u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hbLog := (abs_le.mp (abs_mul_log_le_one hbabs)).2
  have hcLog := (abs_le.mp (abs_mul_log_le_one hcabs)).1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlength : c - b ≤ 1 := by linarith
  nlinarith

/-- A radius avoiding all finitely many prescribed zero moduli and controlling
the sum of the logarithmic losses, with multiplicities. -/
theorem radialLog_select_radius {ι : Type*} (s : Finset ι) (u : ι → ℝ) (m : ι → ℕ)
    {b c : ℝ} (hb : 0 ≤ b) (hbc : b < c) (hc : c ≤ 1)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) (hN : 0 < ∑ i ∈ s, m i) :
    ∃ ρ ∈ Ioo b c, (∀ i ∈ s, ρ ≠ u i) ∧
      (∑ i ∈ s, (m i : ℝ) * radialLog (u i) ρ) ≤
        ((Real.log 2 + 4) / (c - b)) * (∑ i ∈ s, m i : ℕ) := by
  classical
  let N : ℝ := ∑ i ∈ s, (m i : ℝ)
  have hNpos : 0 < N := by dsimp [N]; exact_mod_cast hN
  let C := (Real.log 2 + 4) / (c - b)
  let G : ℝ → ℝ := fun r => ∑ i ∈ s, (m i : ℝ) * radialLog (u i) r
  have hi : IntervalIntegrable G volume b c := by
    have he : (∑ i ∈ s, fun r => (m i : ℝ) * radialLog (u i) r) = G := by
      ext r
      simp [G]
    rw [← he]
    exact IntervalIntegrable.sum s (fun i _ => (radialLog_integrable (u i) b c).const_mul (m i : ℝ))
  have hupper : (∫ r in b..c, G r) ≤ N * (Real.log 2 + 3) := by
    rw [integral_finsetSum (fun i _ => (radialLog_integrable (u i) b c).const_mul (m i : ℝ))]
    simp only [intervalIntegral.integral_const_mul]
    dsimp [N]
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (radialLog_integral_bound hb hbc hc (hu i hi).1 (hu i hi).2) (Nat.cast_nonneg _))
  by_contra hex
  push Not at hex
  have hae : ∀ᵐ r : ℝ, ∀ i : s, r ≠ u i := ae_all_iff.mpr (fun i => volume.ae_ne (u i))
  have hge : (fun _ : ℝ => C * N) ≤ᵐ[volume.restrict (Icc b c)] G := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_of_ae (volume.ae_ne b),
      ae_restrict_of_ae (volume.ae_ne c), self_mem_ae_restrict measurableSet_Icc] with r hr hrb hrc hri
    have hri' : r ∈ Ioo b c := ⟨lt_of_le_of_ne hri.1 hrb.symm, lt_of_le_of_ne hri.2 hrc⟩
    have hneq : ∀ i ∈ s, r ≠ u i := fun i hi => hr ⟨i, hi⟩
    have h := hex r hri' hneq
    have hcast : ((∑ i ∈ s, m i : ℕ) : ℝ) = N := by simp [N]
    exact le_of_lt (by simpa only [hcast] using h)
  have hlower := integral_mono_ae_restrict hbc.le intervalIntegrable_const hi hge
  rw [intervalIntegral.integral_const] at hlower
  change (c - b) * (C * N) ≤ _ at hlower
  have hC : (c - b) * C = Real.log 2 + 4 := mul_div_cancel₀ _ (sub_ne_zero.mpr hbc.ne')
  rw [← mul_assoc, hC] at hlower
  nlinarith

theorem radialLog_select_radius_with_weights {ι : Type*} (s : Finset ι) (u : ι → ℝ) (m : ι → ℕ)
    {b c : ℝ} (hb : 0 ≤ b) (hbc : b < c) (hc : c ≤ 1)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) (hm : ∀ i ∈ s, 0 < m i) :
    ∃ ρ ∈ Ioo b c, (∀ i ∈ s, ρ ≠ u i) ∧
      (∑ i ∈ s, (m i : ℝ) * radialLog (u i) ρ) ≤
        ((Real.log 2 + 4) / (c - b)) * (∑ i ∈ s, m i : ℕ) := by
  by_cases hN : 0 < ∑ i ∈ s, m i
  · exact radialLog_select_radius s u m hb hbc hc hu hN
  · have hs : s = ∅ := by
      ext i
      simp only [Finset.notMem_empty, iff_false]
      intro hi
      have hle := Finset.single_le_sum (fun j (_ : j ∈ s) => Nat.zero_le (m j)) hi
      have := hm i hi
      omega
    subst s
    exact ⟨(b + c) / 2, ⟨by linarith, by linarith⟩, by simp, by simp⟩

end ModifiedCartan
