import ModifiedCartan.SharpTwoEndpoints
import ModifiedCartan.ScaledPseudodiameter
import ModifiedCartan.InteriorGrowthRadii
import ModifiedCartan.CombinationNorm

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

/-- Data constructed from failure of both reciprocal alternatives, not additional
assumptions in the sharp two-term theorem. -/
structure SharpTwoSetup (A a : Fin 2 → ℕ → ℂ → ℂ) (s : ℂ → ℂ) (Ω : Set ℂ) where
  L : Set ℂ
  compact : IsCompact L
  nonempty : L.Nonempty
  subset : L ⊆ Ω
  nonzero : ∀ z ∈ L, s z ≠ 0
  r : ℝ
  α : ℝ
  β : ℝ
  v : ℝ
  q : ℝ
  C₀ : ℝ
  ell : ℝ
  c : ℝ
  r_pos : 0 < r
  r_lt : r < α
  α_lt : α < β
  β_lt : β < v
  v_lt : v < 1
  q_pos : 0 < q
  q_lt : q < sharpRadius
  C₀_nonneg : 0 ≤ C₀
  ell_pos : 0 < ell
  c_pos : 0 < c
  contained : L ⊆ closedBall 0 r
  point : Fin 2 → ℕ → ℂ
  point_mem : ∀ i n, point i n ∈ L
  ρ : ℕ → ℝ
  radius : ∀ n, α ≤ ρ n ∧ ρ n < β
  pseudodistance : ∀ R ∈ Icc α 1, ∀ z ∈ L, ∀ w ∈ L,
    z / (R : ℂ) ∈ disk 1 ∧ w / (R : ℂ) ∈ disk 1 ∧
    ‖diskAutomorphism (z / (R : ℂ)) (w / (R : ℂ))‖ ≤ symmetricPseudodistance q
  failure : ∀ᶠ n in atTop, ∀ i, Real.log ‖A i n (point i n)‖ ≤ C₀
  endpoint_zero : Tendsto (fun n => a 0 n (point 0 n) / (∑ i, a i n (point 0 n))) atTop (𝓝 0)
  endpoint_one : Tendsto (fun n => a 0 n (point 1 n) / (∑ i, a i n (point 1 n))) atTop (𝓝 1)
  interior_norms : ∀ᶠ n in atTop, ∀ i, ell ≤ diskSupNorm (a i n) r
  lower_sum : ∀ᶠ n in atTop, ∀ z ∈ L, c ≤ ‖∑ i, a i n z‖
  growth : Tendsto (fun n => unitGrowthMean (fun i => A i n) (ρ n)) atTop atTop
  controlled : ∀ᶠ n in atTop,
    0 < unitGrowthMean (fun i => A i n) (ρ n) ∧
    ρ n + 1 / unitGrowthMean (fun i => A i n) (ρ n) < β ∧
    unitGrowthMean (fun i => A i n) (ρ n + 1 / unitGrowthMean (fun i => A i n) (ρ n)) ≤
      2 * unitGrowthMean (fun i => A i n) (ρ n) ∧
    (∀ z ∈ sphere (0 : ℂ) (ρ n), ∃ i, 1 < ‖A i n z‖) ∧
    (∀ i z, ‖z‖ ≤ v → ‖a i n z‖ ≤ ‖A i n z‖)

theorem sharp_two_setup {A a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hΩ1 : Ω ⊆ disk 1) (hdiam : HasHyperbolicDiameterLE Ω (Real.log 3))
    (hA : ∀ i n, IsHolomorphicUnit (A i n) (disk 1))
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsmall : ∀ i, CompactConvergence (fun n z => a i n z / A i n z) 0 (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    (hsne : ∃ z ∈ disk 1, s z ≠ 0)
    (hno : ∀ i, ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CompactConvergence
      (fun n z => (A i (φ n) z)⁻¹) 0 Ω) : Nonempty (SharpTwoSetup A a s Ω) := by
  have hs := compactConvergence_holomorphic isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
  obtain ⟨L, hL, hLne, hLΩ, hnz, C₀, hC₀, z, hz, hlog⟩ :=
    zero_free_finite_failure_points A hs hsne hΩ hΩ1 hA hno
  obtain ⟨c, hc, hlow, _, hzero, hone, hnorm⟩ :=
    two_term_failure_limits hA ha hsmall hsum hL (hLΩ.trans hΩ1) hnz hz hlog
  obtain ⟨r, hr, hr1, hLr⟩ := compact_subset_unit_closedDisk hL hLne (hLΩ.trans hΩ1)
  obtain ⟨q, ρ₀, hq, hqr, hρ₀, hρ₀1, hpseudo⟩ := compact_scaled_pseudodiameter hΩ hΩ1 hdiam hL hLne hLΩ
  let l := max r ρ₀
  let u := (l + 1) / 2
  let v := (u + 1) / 2
  have hl : 0 ≤ l := hr.le.trans (le_max_left _ _)
  have hl1 : l < 1 := max_lt hr1 hρ₀1
  have hlu : l < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  have huv : u < v := by dsimp [v]; linarith
  have hv1 : v < 1 := by dsimp [v]; linarith
  obtain ⟨α, β, _, ρ, hα, hαβ, hβ, _, hρ, hM, hgood⟩ :=
    interior_absorption_growth_radii hl hlu huv hv1 (by norm_num : 0 < 2) hA ha hsmall hsum hsne
  have hnorms : ∀ᶠ n in atTop, ∀ i, c / 2 ≤ diskSupNorm (a i n) r := by
    filter_upwards [hnorm] with n hn i
    have hsup : ∀ j k : Fin 2, ‖a j n (z k n)‖ ≤ diskSupNorm (a j n) r := by
      intro j k
      exact le_csSup ((isCompact_closedBall (0 : ℂ) r).bddAbove_image
        ((ha j n).continuousOn.mono (closedBall_subset_ball hr1)).norm)
        (mem_image_of_mem _ (hLr (hz k n)))
    fin_cases i
    · exact hn.2.trans (hsup 0 1)
    · exact hn.1.trans (hsup 1 0)
  refine ⟨{
    L := L, compact := hL, nonempty := hLne, subset := hLΩ, nonzero := hnz
    r := r, α := α, β := β, v := v, q := q, C₀ := C₀, ell := c / 2, c := c
    r_pos := hr, r_lt := (le_max_left _ _).trans_lt hα, α_lt := hαβ, β_lt := hβ.trans huv
    v_lt := hv1, q_pos := hq, q_lt := hqr, C₀_nonneg := hC₀, ell_pos := half_pos hc, c_pos := hc
    contained := hLr, point := z, point_mem := hz, ρ := ρ, radius := hρ
    pseudodistance := ?_, failure := hlog, endpoint_zero := hzero, endpoint_one := hone
    interior_norms := hnorms, lower_sum := hlow, growth := hM, controlled := ?_ }⟩
  · intro R hR a haL b hbL
    exact hpseudo R ⟨(le_max_right _ _).trans (hα.le.trans hR.1), hR.2⟩ a haL b hbL
  · filter_upwards [hgood] with n hn
    refine ⟨hn.1, hn.2.1, hn.2.2.1, ?_, hn.2.2.2.2⟩
    intro w hw
    have hwn : ‖w‖ = ρ n := by simpa only [mem_sphere, dist_zero_right] using hw
    exact (hn.2.2.2.1 w (by rw [hwn]; exact (hρ n).1) (by rw [hwn]; exact (hρ n).2.le)).2

end ModifiedCartan
