import ModifiedCartan.CartanScaled
import ModifiedCartan.WronskianCircle
import ModifiedCartan.WronskianPower

noncomputable section
set_option autoImplicit false
open Metric Set
namespace ModifiedCartan

/-- Full quantitative Wronskian estimate, Proposition `prop:wronskian`. -/
theorem quantitativeWronskian_proved : QuantitativeWronskian := by
  intro m hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  clear hm
  induction n with
  | zero =>
    intro a b ha hab hb
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro g hg _hbound
    simpa only [Real.rpow_one, one_mul] using quantitativeWronskian_one g ha.le hab.le
      (fun j => (hg j).continuousOn.mono (closedBall_subset_ball hb))
  | succ n ih =>
    intro a b ha hab hb
    let b₁ := (3 * a + b) / 4
    let b₂ := (a + b) / 2
    let b₃ := (a + 3 * b) / 4
    let S := (b + 1) / 2
    have hab₁ : a < b₁ := by dsimp [b₁]; linarith
    have hb₁₂ : b₁ < b₂ := by dsimp [b₁, b₂]; linarith
    have hb₂₃ : b₂ < b₃ := by dsimp [b₂, b₃]; linarith
    have hb₃b : b₃ < b := by dsimp [b₃]; linarith
    have hbS : b < S := by dsimp [S]; linarith
    have hS1 : S < 1 := by dsimp [S]; linarith
    have hb₁ : 0 < b₁ := ha.trans hab₁
    have hb₁1 : b₁ < 1 := hb₁₂.trans (hb₂₃.trans (hb₃b.trans hb))
    obtain ⟨c₁, K₁, hc₁, hK₁, hind⟩ := ih a b₁ ha hab₁ hb₁1
    obtain ⟨γ, hγ, hcartan⟩ := cartan_circle_scaled hb₁ hb₁₂ hb₂₃ (hb₃b.trans hbS)
    let M := wronskianUpperBound (n + 1) S
    have hM : 0 < M := wronskianUpperBound_pos _ hS1
    let β := K₁ * γ
    let d := M * (c₁ / M) ^ γ
    let A := wronskianCircleConstant (n + 1) b
    have hA : 0 < A := wronskianCircleConstant_pos (by omega) hb
    have hd : 0 < d := mul_pos hM (Real.rpow_pos_of_pos (div_pos hc₁ hM) _)
    let K : ℝ := max ((n + 2 : ℕ) : ℝ) (2 * β + 1)
    refine ⟨d ^ 2 / A, K, div_pos (sq_pos_of_pos hd) hA, le_max_left _ _, ?_⟩
    intro g hg hbound
    let τ := leastCombinationNorm g a
    have hga : ∀ j, AnalyticOnNhd ℂ (g j) (disk 1) := fun j => (hg j).analyticOnNhd isOpen_ball
    have hgcont : ∀ j, ContinuousOn (g j) (closedBall (0 : ℂ) a) :=
      fun j => (hg j).continuousOn.mono (closedBall_subset_ball (hab.trans hb))
    have hτ0 : 0 ≤ τ := leastCombinationNorm_nonneg (by omega) ha.le hgcont
    have hτ1 : τ ≤ 1 := leastCombinationNorm_le_one (by omega) ha.le hgcont
      (fun j z hz => hbound j z (closedBall_subset_ball (hab.trans hb) hz))
    have hΔ0 : 0 ≤ diskSupNorm (wronskian g) b := diskSupNorm_nonneg (ha.le.trans hab.le)
      ((wronskian_analyticOnNhd hga).continuousOn.mono (closedBall_subset_ball hb))
    by_cases hτzero : τ = 0
    · change d ^ 2 / A * τ ^ K ≤ _
      have hKpos : 0 < K := lt_of_lt_of_le (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ)) (le_max_left _ _)
      simpa only [hτzero, Real.zero_rpow hKpos.ne', mul_zero] using hΔ0
    have hτ : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτzero)
    let V := wronskian (fun j : Fin (n + 1) => g j.castSucc)
    have hVhol : DifferentiableOn ℂ V (disk S) :=
      (wronskian_analyticOnNhd (fun j : Fin (n + 1) => hga j.castSucc)).differentiableOn.mono
        (ball_subset_ball hS1.le)
    have hVbound : ∀ z ∈ disk S, ‖V z‖ ≤ M := by
      intro z hz
      apply wronskian_unit_disk_bound (fun j => hg j.castSucc) (fun j => hbound j.castSucc) hS1
      exact (show ‖z‖ < S by simpa [disk] using hz).le
    have htV : c₁ * τ ^ K₁ ≤ diskSupNorm V b₁ := by
      apply le_trans _ (hind (fun j => g j.castSucc) (fun j => hg j.castSucc) (fun j => hbound j.castSucc))
      apply mul_le_mul_of_nonneg_left _ hc₁.le
      exact Real.rpow_le_rpow hτ0
        (leastCombinationNorm_initial_subfamily (by omega) ha.le hgcont)
        (le_trans (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) hK₁)
    obtain ⟨ρ, hρlo, hρhi, hρbound⟩ := hcartan V M (c₁ * τ ^ K₁) hVhol hVbound hM
      (mul_pos hc₁ (Real.rpow_pos_of_pos hτ _)) htV
    have hv : 0 < d * τ ^ β := mul_pos hd (Real.rpow_pos_of_pos hτ _)
    have hVcircle : ∀ z, ‖z‖ = ρ → d * τ ^ β ≤ ‖V z‖ := by
      intro z hz
      have he := hρbound z hz
      rw [scaled_cartan_power hτ0 hc₁ hM] at he
      exact he
    have hcircle := wronskian_circle_lower_bound ha.le
      (hab₁.trans (hb₁₂.trans hρlo)) (hρhi.trans hb₃b) hb hv hg hbound hVcircle
    exact wronskian_power_algebra hτ hτ1 hA hd (le_max_right _ _) hcircle

end ModifiedCartan
