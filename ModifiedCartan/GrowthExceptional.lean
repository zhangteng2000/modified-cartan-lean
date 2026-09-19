import ModifiedCartan.Growth
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped ENNReal
namespace ModifiedCartan

/-- Radii with an admissible outward step but growth by more than a factor two. -/
def growthBadRadii (M : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {r | r ∈ Icc a b ∧ r + 1/M r ≤ b ∧ 2*M r < M (r + 1/M r)}

/-- Quantitative Borel growth lemma: the bad radii have total length at most
2/M(a). A dyadic sublevel-set covering supplies the actual measure bound. -/
theorem growthBadRadii_measure_le {M : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn M (Icc a b)) (hm : MonotoneOn M (Icc a b)) (ha : 0 < M a) :
    volume (growthBadRadii M a b) ≤ ENNReal.ofReal (2/M a) := by
  classical
  have hex : ∀ k : ℕ, ∃ x : ℝ, x ∈ Icc a b ∧ M x ≤ 2^(k+1)*M a ∧
      ∀ r ∈ Icc a b, M r ≤ 2^(k+1)*M a → r ≤ x := by
    intro k
    let S := Icc a b ∩ M ⁻¹' Iic (2^(k+1)*M a)
    have hS : IsCompact S := hc.lowerSemicontinuousOn.isCompact_inter_preimage_Iic isCompact_Icc _
    have hpow : (1 : ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
    have hne : S.Nonempty := ⟨a,⟨⟨le_rfl,hab⟩,by change M a ≤ 2^(k+1)*M a; nlinarith⟩⟩
    obtain ⟨x,hx,hmax⟩ := hS.exists_isMaxOn hne continuous_id.continuousOn
    exact ⟨x,hx.1,hx.2,fun r hr hMr => hmax ⟨hr,hMr⟩⟩
  choose x hx hMx hmax using hex
  let e : ℕ → ℝ := fun k => (1/M a)*(1/2)^k
  have he : ∀ k, e k = 1/(2^k*M a) := by
    intro k
    dsimp [e]
    rw [div_pow,one_pow]
    ring
  have he0 : ∀ k, 0 ≤ e k := fun k => mul_nonneg (one_div_nonneg.mpr ha.le) (by positivity)
  have hsub : growthBadRadii M a b ⊆ ⋃ k : ℕ, Icc (x k - e k) (x k) := by
    rintro r ⟨hr,hrstep,hgrowth⟩
    have hMar : M a ≤ M r := hm ⟨le_rfl,hab⟩ hr hr.1
    have hMr : 0 < M r := ha.trans_le hMar
    obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near ((one_le_div ha).mpr hMar) (by norm_num : (1 : ℝ) < 2)
    have hlow : 2^k*M a ≤ M r := (le_div_iff₀ ha).mp hk
    have hhigh : M r < 2^(k+1)*M a := (div_lt_iff₀ ha).mp hk'
    have hrx : r ≤ x k := hmax k r hr hhigh.le
    have hxstep : x k < r + 1/M r := by
      by_contra hnot
      have hstep : r+1/M r ∈ Icc a b := ⟨hr.1.trans (le_add_of_nonneg_right (one_div_pos.mpr hMr).le),hrstep⟩
      have horder := hm hstep (hx k) (le_of_not_gt hnot)
      have hthreshold : 2^(k+1)*M a ≤ 2*M r := by
        rw [pow_succ]
        nlinarith
      linarith [hMx k]
    have hrecip : 1/M r ≤ e k := by
      rw [he]
      exact one_div_le_one_div_of_le (mul_pos (by positivity) ha) hlow
    apply mem_iUnion.mpr
    exact ⟨k,⟨by linarith,hrx⟩⟩
  calc
    volume (growthBadRadii M a b) ≤ volume (⋃ k : ℕ, Icc (x k-e k) (x k)) := measure_mono hsub
    _ ≤ ∑' k : ℕ, volume (Icc (x k-e k) (x k)) := measure_iUnion_le _
    _ = ∑' k : ℕ, ENNReal.ofReal (e k) := by simp only [Real.volume_Icc,sub_sub_cancel]
    _ = ENNReal.ofReal (2/M a) := by
      simp only [e]
      simp_rw [ENNReal.ofReal_mul (one_div_nonneg.mpr ha.le),ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/2)]
      have hhalf : ENNReal.ofReal (1/2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_one,ENNReal.ofReal_ofNat,one_div]
      rw [hhalf,ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two]
      have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [htwo,← ENNReal.ofReal_mul (one_div_nonneg.mpr ha.le)]
      congr 1
      ring

/-- Adding the terminal interval also controls radii whose step would leave
the prescribed interval. -/
theorem growthBadRadii_or_exit_measure_le {M : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn M (Icc a b)) (hm : MonotoneOn M (Icc a b)) (ha : 0 < M a) :
    volume {r | r ∈ Icc a b ∧ (b < r+1/M r ∨ 2*M r < M (r+1/M r))} ≤
      ENNReal.ofReal (3/M a) := by
  have hsub : {r | r ∈ Icc a b ∧ (b < r+1/M r ∨ 2*M r < M (r+1/M r))} ⊆
      growthBadRadii M a b ∪ Icc (b-1/M a) b := by
    rintro r ⟨hr,hbad⟩
    have hMar : M a ≤ M r := hm ⟨le_rfl,hab⟩ hr hr.1
    have hinv : 1/M r ≤ 1/M a := one_div_le_one_div_of_le ha hMar
    by_cases he : b < r+1/M r
    · exact Or.inr ⟨by linarith,hr.2⟩
    · exact Or.inl ⟨hr,le_of_not_gt he,hbad.resolve_left he⟩
  have hb := growthBadRadii_measure_le hab hc hm ha
  calc
    _ ≤ volume (growthBadRadii M a b ∪ Icc (b-1/M a) b) := measure_mono hsub
    _ ≤ volume (growthBadRadii M a b) + volume (Icc (b-1/M a) b) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2/M a) + ENNReal.ofReal (1/M a) := by
      simpa only [Real.volume_Icc,sub_sub_cancel] using add_le_add hb (le_refl (volume (Icc (b-1/M a) b)))
    _ = ENNReal.ofReal (3/M a) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Growth selection still succeeds inside any prescribed set of radii
whose outer measure exceeds the explicit bad-radius budget. -/
theorem exists_growth_radius_in_large_set {M : ℝ → ℝ} {a b : ℝ} {S : Set ℝ}
    (hab : a ≤ b) (hc : ContinuousOn M (Icc a b)) (hm : MonotoneOn M (Icc a b))
    (ha : 0 < M a) (hS : S ⊆ Icc a b)
    (hsize : ENNReal.ofReal (3/M a) < volume S) :
    ∃ r ∈ S, r + 1/M r ≤ b ∧ M (r+1/M r) ≤ 2*M r := by
  by_contra hn
  push Not at hn
  have hsub : S ⊆ {r | r ∈ Icc a b ∧ (b < r+1/M r ∨ 2*M r < M (r+1/M r))} := by
    intro r hr
    refine ⟨hS hr,?_⟩
    by_cases h : r+1/M r ≤ b
    · exact Or.inr (hn r hr h)
    · exact Or.inl (lt_of_not_ge h)
  have hb := (measure_mono hsub).trans (growthBadRadii_or_exit_measure_le hab hc hm ha)
  exact (not_lt_of_ge hb) hsize

end ModifiedCartan

