import ModifiedCartan.Radii

noncomputable section
namespace ModifiedCartan

def poissonDenom (s c : ℝ) : ℝ := 1 - 2 * s * c + s ^ 2
def poissonKernel (s c : ℝ) : ℝ := (1 - s ^ 2) / poissonDenom s c
def weightedKernel (t c : ℝ) : ℝ := (1 - t) ^ 2 / poissonDenom t c

theorem poissonDenom_pos {s c : ℝ} (hs : |s| < 1) (hc : |c| ≤ 1) :
    0 < poissonDenom s c := by
  have hs' := abs_lt.mp hs
  have hc' := abs_le.mp hc
  unfold poissonDenom
  have hsq : s ^ 2 < 1 := by nlinarith [sq_abs s]
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have h : (s * c) ^ 2 ≤ s ^ 2 := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hc2)]
  nlinarith [sq_nonneg (1 - s * c)]

theorem poissonKernel_pos {s c : ℝ} (hs : |s| < 1) (hc : |c| ≤ 1) :
    0 < poissonKernel s c := by
  have hs' := abs_lt.mp hs
  exact div_pos (by nlinarith) (poissonDenom_pos hs hc)

/-- Exact factorization (5.3), without any analytic hypotheses. -/
theorem kernel_factorization {s c : ℝ} (hs : |s| < 1) (hc : |c| ≤ 1) :
    (1 - s) / ((1 + s) * (2 + c)) + (1 + s) / ((1 - s) * (2 - c)) -
      poissonKernel s c =
    (((1 + s ^ 2) * c - 2 * s) ^ 2 + 12 * s ^ 2 * (1 - c ^ 2)) /
      ((1 - s ^ 2) * (4 - c ^ 2) * poissonDenom s c) := by
  have hs' := abs_lt.mp hs
  have hc' := abs_le.mp hc
  have h1 : 1 + s ≠ 0 := by linarith
  have h2 : 1 - s ≠ 0 := by linarith
  have h3 : 2 + c ≠ 0 := by linarith
  have h4 : 2 - c ≠ 0 := by linarith
  have h5 : 1 - s ^ 2 ≠ 0 := by nlinarith
  have h6 : 4 - c ^ 2 ≠ 0 := by nlinarith
  have h7 := ne_of_gt (poissonDenom_pos hs hc)
  unfold poissonKernel
  field_simp
  unfold poissonDenom
  ring

theorem kernel_boundary_nonneg {s c : ℝ} (hs : |s| < 1) (hc : |c| ≤ 1) :
    poissonKernel s c ≤
      (1 - s) / ((1 + s) * (2 + c)) + (1 + s) / ((1 - s) * (2 - c)) := by
  have hs' := abs_lt.mp hs
  have hc' := abs_le.mp hc
  have hnum : 0 ≤ ((1 + s ^ 2) * c - 2 * s) ^ 2 + 12 * s ^ 2 * (1 - c ^ 2) := by
    have hc2 : 0 ≤ 1 - c ^ 2 := by nlinarith
    positivity
  have hden : 0 < (1 - s ^ 2) * (4 - c ^ 2) * poissonDenom s c := by
    apply mul_pos
    · apply mul_pos <;> nlinarith
    · exact poissonDenom_pos hs hc
  have h := div_nonneg hnum hden.le
  rw [← kernel_factorization hs hc] at h
  linarith

theorem weightedKernel_difference {t r c : ℝ}
    (ht : |t| < 1) (hr : |r| < 1) (hc : |c| ≤ 1) :
    weightedKernel t c - weightedKernel r c =
      2 * (r - t) * (1 - c) * (1 - r * t) /
        (poissonDenom t c * poissonDenom r c) := by
  have h1 := ne_of_gt (poissonDenom_pos ht hc)
  have h2 := ne_of_gt (poissonDenom_pos hr hc)
  unfold weightedKernel
  field_simp
  unfold poissonDenom
  ring

theorem weightedKernel_antitone {t r c : ℝ}
    (ht : 0 ≤ t) (htr : t ≤ r) (hr : r < 1) (hc : |c| ≤ 1) :
    weightedKernel r c ≤ weightedKernel t c := by
  have ht1 : |t| < 1 := by rw [abs_of_nonneg ht]; linarith
  have hr1 : |r| < 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ r)]; exact hr
  have hc' := abs_le.mp hc
  have hprod : 0 ≤ 1 - r * t := by nlinarith
  have hn : 0 ≤ 2 * (r - t) * (1 - c) * (1 - r * t) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr htr))
      (sub_nonneg.mpr hc'.2)) hprod
  have hd : 0 ≤ poissonDenom t c * poissonDenom r c :=
    mul_nonneg (poissonDenom_pos ht1 hc).le (poissonDenom_pos hr1 hc).le
  have h := div_nonneg hn hd
  rw [← weightedKernel_difference ht1 hr1 hc] at h
  linarith

theorem weightedKernel_strict {t r c : ℝ}
    (ht : 0 ≤ t) (htr : t < r) (hr : r < 1) (hc : |c| ≤ 1) (hc1 : c < 1) :
    weightedKernel r c < weightedKernel t c := by
  have ht1 : |t| < 1 := by rw [abs_of_nonneg ht]; linarith
  have hr1 : |r| < 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ r)]; exact hr
  have hprod : 0 < 1 - r * t := by nlinarith
  have hn : 0 < 2 * (r - t) * (1 - c) * (1 - r * t) := by positivity
  have hd : 0 < poissonDenom t c * poissonDenom r c :=
    mul_pos (poissonDenom_pos ht1 hc) (poissonDenom_pos hr1 hc)
  have h := div_pos hn hd
  rw [← weightedKernel_difference ht1 hr1 hc] at h
  linarith

theorem weightedKernel_at_sharp {c : ℝ} (hc : |c| ≤ 1) :
    weightedKernel sharpRadius c = 1 / (2 - c) := by
  have h1 : |sharpRadius| < 1 := by
    rw [abs_of_pos sharpRadius_pos]; exact sharpRadius_lt_one
  have h2 := ne_of_gt (poissonDenom_pos h1 hc)
  have h3 : 2 - c ≠ 0 := by have := (abs_le.mp hc).2; linarith
  unfold weightedKernel
  field_simp
  unfold poissonDenom
  have hq := congrArg (fun x : ℝ => x * (2 - c)) sharpRadius_quadratic
  nlinarith [sharpRadius_quadratic]

def twoPointKernel (t s c : ℝ) : ℝ :=
  (1 - s) / (1 + s) * weightedKernel t (-c) +
  (1 + s) / (1 - s) * weightedKernel t c

/-- The strict pointwise kernel comparison underlying Lemma 5.1. -/
theorem twoPointKernel_strict_aux {t s c : ℝ} (ht : 0 ≤ t) (htr : t < sharpRadius)
    (hs1 : |s| < 1) (hc : |c| ≤ 1) : poissonKernel s c < twoPointKernel t s c := by
  have hs' := abs_lt.mp hs1
  have hcn : |-c| ≤ 1 := by simpa using hc
  have hw1 : 0 < (1 - s) / (1 + s) := div_pos (by linarith) (by linarith)
  have hw2 : 0 < (1 + s) / (1 - s) := div_pos (by linarith) (by linarith)
  have ha := weightedKernel_antitone ht htr.le sharpRadius_lt_one hc
  have hb := weightedKernel_antitone ht htr.le sharpRadius_lt_one hcn
  have hbase : poissonKernel s c ≤ twoPointKernel sharpRadius s c := by
    simp only [twoPointKernel, weightedKernel_at_sharp hc, weightedKernel_at_sharp hcn,
      sub_neg_eq_add]
    rw [div_mul_div_comm, div_mul_div_comm, mul_one, mul_one]
    exact kernel_boundary_nonneg hs1 hc
  apply lt_of_le_of_lt hbase
  unfold twoPointKernel
  by_cases hc1 : c < 1
  · have hh := weightedKernel_strict ht htr sharpRadius_lt_one hc hc1
    exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hb hw1.le)
      (mul_lt_mul_of_pos_left hh hw2)
  · have hc1' : -c < 1 := by have := (abs_le.mp hc).2; linarith
    have hh := weightedKernel_strict ht htr sharpRadius_lt_one hcn hc1'
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hh hw1)
      (mul_le_mul_of_nonneg_left ha hw2.le)

theorem twoPointKernel_strict {t s c : ℝ} (ht : 0 ≤ t) (htr : t < sharpRadius)
    (hs : |s| ≤ t) (hc : |c| ≤ 1) : poissonKernel s c < twoPointKernel t s c :=
  twoPointKernel_strict_aux ht htr (lt_of_le_of_lt hs (lt_trans htr sharpRadius_lt_one)) hc

/-- Uniform positive gap in the kernel comparison, before integration against
the representing measure of a positive harmonic function. -/
theorem twoPointKernel_uniform {q : ℝ} (_hq : 0 < q) (hqr : q < sharpRadius) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t s c : ℝ, 0 ≤ t → t ≤ q → |s| ≤ t → |c| ≤ 1 →
      (1 + ε) * poissonKernel s c ≤ twoPointKernel t s c := by
  let S : Set (ℝ × ℝ × ℝ) := Set.Icc 0 q ×ˢ Set.Icc (-q) q ×ˢ Set.Icc (-1) 1
  let gap : ℝ × ℝ × ℝ → ℝ := fun x =>
    (twoPointKernel x.1 x.2.1 x.2.2 - poissonKernel x.2.1 x.2.2) /
      poissonKernel x.2.1 x.2.2
  have hcompact : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hq1 : q < 1 := lt_trans hqr sharpRadius_lt_one
  have hcontinuous : ContinuousOn gap S := by
    intro x hx
    have ht : |x.1| < 1 := by rw [abs_of_nonneg hx.1.1]; exact lt_of_le_of_lt hx.1.2 hq1
    have hs : |x.2.1| < 1 := (abs_le.mpr hx.2.1).trans_lt hq1
    have hc : |x.2.2| ≤ 1 := abs_le.mpr hx.2.2
    have hcn : |-x.2.2| ≤ 1 := by simpa using hc
    have h1 : 1 + x.2.1 ≠ 0 := by have := (abs_lt.mp hs).1; linarith
    have h2 : 1 - x.2.1 ≠ 0 := by have := (abs_lt.mp hs).2; linarith
    have h3 := ne_of_gt (poissonDenom_pos ht hc)
    have h4 := ne_of_gt (poissonDenom_pos ht hcn)
    have h5 := ne_of_gt (poissonDenom_pos hs hc)
    have h6 := ne_of_gt (poissonKernel_pos hs hc)
    apply ContinuousAt.continuousWithinAt
    dsimp [gap, twoPointKernel, weightedKernel, poissonKernel, poissonDenom] at *
    fun_prop (disch := assumption)
  have hpositive : ∀ x ∈ S, 0 < gap x := by
    intro x hx
    have hs : |x.2.1| < 1 := (abs_le.mpr hx.2.1).trans_lt hq1
    have hc : |x.2.2| ≤ 1 := abs_le.mpr hx.2.2
    exact div_pos (sub_pos.mpr (twoPointKernel_strict_aux hx.1.1
      (lt_of_le_of_lt hx.1.2 hqr) hs hc)) (poissonKernel_pos hs hc)
  obtain ⟨ε, hε, hbound⟩ := hcompact.exists_forall_le' hcontinuous hpositive
  refine ⟨ε, hε, ?_⟩
  intro t s c ht htq hst hc
  have hsq : |s| ≤ q := hst.trans htq
  have hmem : (t, s, c) ∈ S := ⟨⟨ht, htq⟩, abs_le.mp hsq, abs_le.mp hc⟩
  have hb := hbound (t, s, c) hmem
  have hp := poissonKernel_pos (hsq.trans_lt hq1) hc
  change ε ≤ (twoPointKernel t s c - poissonKernel s c) / poissonKernel s c at hb
  have hh := (le_div_iff₀ hp).mp hb
  nlinarith

end ModifiedCartan
