import ModifiedCartan.UnitGrowth
import ModifiedCartan.ZeroFreeAnnulus
import ModifiedCartan.GrowthSelection
import ModifiedCartan.PoissonEnvelope

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem finite_compactConvergence_zero_bound {ι : Type*} [Fintype ι]
    {f : ι → ℕ → ℂ → ℂ} {U K : Set ℂ}
    (hf : ∀ i, CompactConvergence (f i) 0 U) (hKU : K ⊆ U) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i z, z ∈ K → ‖f i n z‖ < ε := by
  apply eventually_all.mpr
  intro i
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hf i K hKU hK) ε hε] with n hn
  intro z hz
  simpa only [Pi.zero_apply, dist_zero_left] using hn z hz

theorem norm_le_unit_of_small_ratio {a A : ℂ} (hA : A ≠ 0) (h : ‖a / A‖ ≤ 1) :
    ‖a‖ ≤ ‖A‖ := by
  calc
    _ = ‖a / A‖ * ‖A‖ := by rw [← norm_mul, div_mul_cancel₀ _ hA]
    _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := one_mul _

theorem large_unit_of_nonvanishing_sum {m : ℕ} (a A : Fin m → ℂ) {c : ℝ}
    (hc : 0 < c) (hA : ∀ i, A i ≠ 0) (hsum : c ≤ ‖∑ i, a i‖)
    (hsmall : ∀ i, ‖a i / A i‖ < c / (2 * (m + 1 : ℕ))) :
    ∃ i, 1 < ‖A i‖ := by
  by_contra hn
  push Not at hn
  have he : 0 ≤ c / (2 * (m + 1 : ℕ)) := by positivity
  have hb : ∀ i, ‖a i‖ ≤ c / (2 * (m + 1 : ℕ)) := by
    intro i
    calc
      _ = ‖a i / A i‖ * ‖A i‖ := by rw [← norm_mul, div_mul_cancel₀ _ (hA i)]
      _ ≤ (c / (2 * (m + 1 : ℕ))) * 1 :=
        mul_le_mul (hsmall i).le (hn i) (norm_nonneg _) he
      _ = _ := mul_one _
  have ht : ‖∑ i, a i‖ ≤ (m : ℝ) * (c / (2 * (m + 1 : ℕ))) := by
    calc
      _ ≤ ∑ i, ‖a i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin m, c / (2 * (m + 1 : ℕ)) := Finset.sum_le_sum (fun i _ => hb i)
      _ = _ := by simp
  have hden : (0 : ℝ) < 2 * (m + 1 : ℕ) := by positivity
  have hbound := (le_div_iff₀ hden).mp (show c ≤ (m : ℝ) * c / (2 * (m + 1 : ℕ)) by
    simpa only [mul_div_assoc] using hsum.trans ht)
  norm_num only [Nat.cast_add, Nat.cast_one] at hbound
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- A fixed zero-free annulus, controlled growth radii, and positive boundary maxima
are all constructed from the original absorption hypotheses. -/
theorem absorption_growth_radii {m : ℕ} (hm : 0 < m)
    {A a : Fin m → ℕ → ℂ → ℂ} {s : ℂ → ℂ}
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk 1))
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) 0 (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    (hsne : ∃ z ∈ disk 1, s z ≠ 0) :
    ∃ α β c : ℝ, ∃ ρ : ℕ → ℝ,
      1 / 2 < α ∧ α < β ∧ β < 3 / 4 ∧ 0 < c ∧
      (∀ n, α ≤ ρ n ∧ ρ n < β) ∧
      Tendsto (fun n => unitGrowthMean (fun i => A i n) (ρ n)) atTop atTop ∧
      ∀ᶠ n in atTop,
        (0 < unitGrowthMean (fun i => A i n) (ρ n)) ∧
        (ρ n + 1 / unitGrowthMean (fun i => A i n) (ρ n) < β) ∧
        (unitGrowthMean (fun i => A i n) (ρ n + 1 / unitGrowthMean (fun i => A i n) (ρ n)) ≤
          2 * unitGrowthMean (fun i => A i n) (ρ n)) ∧
        (∀ z : ℂ, α ≤ ‖z‖ → ‖z‖ ≤ β → c ≤ ‖∑ i, a i n z‖ ∧ ∃ i, 1 < ‖A i n z‖) ∧
        (∀ i z, ‖z‖ ≤ 7 / 8 → ‖a i n z‖ ≤ ‖A i n z‖) := by
  have hs := compactConvergence_holomorphic isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
  obtain ⟨α, β, hα, hαβ, hβ, hnz⟩ := exists_zero_free_annulus hs hsne
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)
  let K : Set ℂ := {z | α ≤ ‖z‖ ∧ ‖z‖ ≤ β}
  have hK : IsCompact K := by
    apply (isCompact_closedBall (0 : ℂ) β).of_isClosed_subset
    · exact isClosed_le continuous_const continuous_norm |>.inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz
      simpa only [mem_closedBall, dist_zero_right] using hz.2
  have hKU : K ⊆ disk 1 := by
    intro z hz
    simpa only [disk, mem_ball, dist_zero_right] using hz.2.trans_lt (hβ.trans (by norm_num))
  obtain ⟨c, hc, hlower⟩ := compactConvergence_eventually_lower_bound hsum hKU hK
    (hs.continuousOn.mono hKU) (fun z hz => hnz z hz.1 hz.2)
  have hsm := finite_compactConvergence_zero_bound hsmall hKU hK
    (ε := c / (2 * (m + 1 : ℕ))) (by positivity)
  have hdom := finite_compactConvergence_zero_bound hsmall
    (closedBall_subset_ball (by norm_num : (7 / 8 : ℝ) < 1))
    (isCompact_closedBall (0 : ℂ) (7 / 8)) (ε := 1) (by norm_num)
  have hinterval : Icc α β ⊆ Ico (0 : ℝ) 1 := by
    intro t ht
    exact ⟨(by linarith [ht.1]), ht.2.trans_lt (hβ.trans (by norm_num))⟩
  obtain ⟨ρ, hρ, hM, hgood⟩ := select_growth_radii
    (fun n => unitGrowthMean (fun i => A i n)) hαβ
    (fun n => (unitGrowthMean_continuousOn (fun i => hA i n)).mono hinterval)
    (fun n => (unitGrowthMean_monotoneOn (fun i => hA i n)).mono hinterval)
    (unitGrowthMean_tendsto_atTop hm A a s hA ha hsmall hsum hsne (by linarith) (by linarith))
  refine ⟨α, β, c, ρ, hα, hαβ, hβ, hc, hρ, hM, ?_⟩
  filter_upwards [hgood, hlower, hsm, hdom] with n hgn hln hsn hdn
  refine ⟨hgn.1, hgn.2.1, hgn.2.2, ?_, ?_⟩
  · intro z hzα hzβ
    have hz : z ∈ K := ⟨hzα, hzβ⟩
    exact ⟨hln z hz, large_unit_of_nonvanishing_sum (fun i => a i n z) (fun i => A i n z)
      hc (fun i => (hA i n).2 z (hKU hz)) (hln z hz) (fun i => hsn i z hz)⟩
  · intro i z hz
    have hzK : z ∈ closedBall (0 : ℂ) (7 / 8) := by simpa using hz
    exact norm_le_unit_of_small_ratio ((hA i n).2 z
      (closedBall_subset_ball (by norm_num : (7 / 8 : ℝ) < 1) hzK)) (hdn i z hzK).le

end ModifiedCartan
