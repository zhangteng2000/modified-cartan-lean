import ModifiedCartan.AbsorptionGrowth

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- A fixed zero-free annulus, controlled growth radii, and positive boundary maxima
are all constructed from the original absorption hypotheses. -/
theorem interior_absorption_growth_radii {l u v : ℝ}
    (hl : 0 ≤ l) (hlu : l < u) (huv : u < v) (hv : v < 1) {m : ℕ} (hm : 0 < m)
    {A a : Fin m → ℕ → ℂ → ℂ} {s : ℂ → ℂ}
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk 1))
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) 0 (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    (hsne : ∃ z ∈ disk 1, s z ≠ 0) :
    ∃ α β c : ℝ, ∃ ρ : ℕ → ℝ,
      l < α ∧ α < β ∧ β < u ∧ 0 < c ∧
      (∀ n, α ≤ ρ n ∧ ρ n < β) ∧
      Tendsto (fun n => unitGrowthMean (fun i => A i n) (ρ n)) atTop atTop ∧
      ∀ᶠ n in atTop,
        (0 < unitGrowthMean (fun i => A i n) (ρ n)) ∧
        (ρ n + 1 / unitGrowthMean (fun i => A i n) (ρ n) < β) ∧
        (unitGrowthMean (fun i => A i n) (ρ n + 1 / unitGrowthMean (fun i => A i n) (ρ n)) ≤
          2 * unitGrowthMean (fun i => A i n) (ρ n)) ∧
        (∀ z : ℂ, α ≤ ‖z‖ → ‖z‖ ≤ β → c ≤ ‖∑ i, a i n z‖ ∧ ∃ i, 1 < ‖A i n z‖) ∧
        (∀ i z, ‖z‖ ≤ v → ‖a i n z‖ ≤ ‖A i n z‖) := by
  have hs := compactConvergence_holomorphic isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
  obtain ⟨α, β, hα, hαβ, hβ, hnz⟩ := exists_zero_free_annulus hs hsne
    hl hlu (huv.trans hv)
  let K : Set ℂ := {z | α ≤ ‖z‖ ∧ ‖z‖ ≤ β}
  have hK : IsCompact K := by
    apply (isCompact_closedBall (0 : ℂ) β).of_isClosed_subset
    · exact isClosed_le continuous_const continuous_norm |>.inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz
      simpa only [mem_closedBall, dist_zero_right] using hz.2
  have hKU : K ⊆ disk 1 := by
    intro z hz
    simpa only [disk, mem_ball, dist_zero_right] using hz.2.trans_lt (hβ.trans (huv.trans hv))
  obtain ⟨c, hc, hlower⟩ := compactConvergence_eventually_lower_bound hsum hKU hK
    (hs.continuousOn.mono hKU) (fun z hz => hnz z hz.1 hz.2)
  have hsm := finite_compactConvergence_zero_bound hsmall hKU hK
    (ε := c / (2 * (m + 1 : ℕ))) (by positivity)
  have hdom := finite_compactConvergence_zero_bound hsmall
    (closedBall_subset_ball hv)
    (isCompact_closedBall (0 : ℂ) v) (ε := 1) (by norm_num)
  have hinterval : Icc α β ⊆ Ico (0 : ℝ) 1 := by
    intro t ht
    exact ⟨(by linarith [ht.1]), ht.2.trans_lt (hβ.trans (huv.trans hv))⟩
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
    have hzK : z ∈ closedBall (0 : ℂ) v := by simpa using hz
    exact norm_le_unit_of_small_ratio ((hA i n).2 z
      (closedBall_subset_ball hv hzK)) (hdn i z hzK).le

end ModifiedCartan
