import ModifiedCartan.Statements

noncomputable section
namespace ModifiedCartan

/-- Lemma 2.4 (Borel--Nevanlinna growth lemma).
The proof uses the invariant t + 2/M(t) ≤ a + 2/M(a).
Monotonicity is unnecessary for this conclusion. -/
theorem growth_lemma (M : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn M (Set.Icc a b))
    (hpos : ∀ x ∈ Set.Icc a b, 0 < M x) (hgap : 2 / M a < b - a) :
    ∃ ρ : ℝ, a ≤ ρ ∧ ρ < b ∧ ρ + 1 / M ρ < b ∧
      M (ρ + 1 / M ρ) ≤ 2 * M ρ := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hMa := hpos a ha
  obtain ⟨xmax, hxmax, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ha⟩ hcont
  by_contra hnot
  have hfail : ∀ t : ℝ, a ≤ t → t < b → t + 1 / M t < b →
      2 * M t < M (t + 1 / M t) := by
    intro t hta htb htstep
    by_contra hn
    exact hnot ⟨t, hta, htb, htstep, le_of_not_gt hn⟩
  have hiter : ∀ n : ℕ, ∃ t : ℝ, a ≤ t ∧ t < b ∧
      t + 2 / M t ≤ a + 2 / M a ∧ (n + 1 : ℝ) * M a ≤ M t := by
    intro n
    induction n with
    | zero => exact ⟨a, le_rfl, hab, le_rfl, by simp⟩
    | succ n ih =>
      obtain ⟨t, hta, htb, hbudget, hlarge⟩ := ih
      have htpos := hpos t ⟨hta, htb.le⟩
      have hinv : 0 < 1 / M t := one_div_pos.mpr htpos
      have htstep : t + 1 / M t < b := by
        have htwo : 2 / M t = 2 * (1 / M t) := by ring
        linarith
      have hnextpos := hpos (t + 1 / M t) ⟨by linarith, htstep.le⟩
      have hdbl := hfail t hta htb htstep
      have hrecip : 2 / M (t + 1 / M t) ≤ 1 / M t := by
        apply (div_le_div_iff₀ hnextpos htpos).mpr
        linarith
      refine ⟨t + 1 / M t, by linarith, htstep, ?_, ?_⟩
      · have htwo : 2 / M t = 2 * (1 / M t) := by ring
        linarith
      · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (M xmax / M a)
  obtain ⟨t, hta, htb, _, hlarge⟩ := hiter n
  have hbnd : M t ≤ M xmax := hmax ⟨hta, htb.le⟩
  have hgreater : M xmax < (n : ℝ) * M a := (div_lt_iff₀ hMa).mp hn
  nlinarith

theorem growthLemma_proved : GrowthLemma := by
  intro M a b hab hcont _hmono hpos hgap
  exact growth_lemma M a b hab hcont hpos hgap

end ModifiedCartan
