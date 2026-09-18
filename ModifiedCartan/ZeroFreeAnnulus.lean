import ModifiedCartan.ZeroFactors
import ModifiedCartan.Convergence
import Mathlib.Order.Interval.Set.Infinite

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem interval_avoiding_finite (s : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ α β : ℝ, a < α ∧ α < β ∧ β < b ∧ ∀ r ∈ Icc α β, r ∉ s := by
  obtain ⟨ρ, hρab, hρs⟩ := (Ioo_infinite hab).exists_notMem_finite s.finite_toSet
  have ho : IsOpen (Ioo a b \ (s : Set ℝ)) := isOpen_Ioo.sdiff s.finite_toSet.isClosed
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp ho ρ ⟨hρab, hρs⟩
  have hmem : ∀ r ∈ Icc (ρ - δ / 2) (ρ + δ / 2), r ∈ ball ρ δ := by
    intro r hr
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hα := hδsub (hmem (ρ - δ / 2) ⟨le_rfl, by linarith⟩)
  have hβ := hδsub (hmem (ρ + δ / 2) ⟨by linarith, le_rfl⟩)
  exact ⟨ρ - δ / 2, ρ + δ / 2, hα.1.1, by linarith, hβ.1.2,
    fun r hr => (hδsub (hmem r hr)).2⟩

/-- Every prescribed interior annular range contains a closed annulus without
zeros of a nontrivial holomorphic function. -/
theorem exists_zero_free_annulus {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (disk 1)) (hFnz : ∃ w ∈ disk 1, F w ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    ∃ α β : ℝ, a < α ∧ α < β ∧ β < b ∧
      ∀ z : ℂ, α ≤ ‖z‖ → ‖z‖ ≤ β → F z ≠ 0 := by
  classical
  obtain ⟨w, hw, hFw⟩ := hFnz
  obtain ⟨s, m, Q, _hs, _hQ, hQnz, hfact⟩ := finite_zero_factorization hF hw hFw (ha.trans hab.le) hb
  obtain ⟨α, β, hα, hαβ, hβ, havoid⟩ := interval_avoiding_finite (s.image norm) hab
  refine ⟨α, β, hα, hαβ, hβ, ?_⟩
  intro z hzα hzβ
  have hzb : z ∈ closedBall (0 : ℂ) b := by simpa using hzβ.trans hβ.le
  rw [hfact z (closedBall_subset_ball hb hzb)]
  apply mul_ne_zero _ (hQnz z hzb)
  apply Finset.prod_ne_zero_iff.mpr
  intro t ht
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro he
  apply havoid ‖z‖ ⟨hzα, hzβ⟩
  exact Finset.mem_image.mpr ⟨t, ht, by rw [he]⟩

theorem compactConvergence_eventually_lower_bound {g : ℕ → ℂ → ℂ} {s : ℂ → ℂ} {U K : Set ℂ}
    (hlim : CompactConvergence g s U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hs : ContinuousOn s K) (hnz : ∀ z ∈ K, s z ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ z ∈ K, c ≤ ‖g n z‖ := by
  obtain ⟨c, hc, hcb⟩ := hK.exists_forall_le' hs.norm (fun z hz => norm_pos_iff.mpr (hnz z hz))
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hlim K hKU hK) (c / 2) (half_pos hc)] with n hn
  intro z hz
  have hdist : ‖s z - g n z‖ < c / 2 := by simpa [dist_eq_norm] using hn z hz
  have htriangle : ‖s z‖ ≤ ‖g n z‖ + ‖s z - g n z‖ := by
    calc
      _ = ‖g n z + (s z - g n z)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith [hcb z hz]

end ModifiedCartan
