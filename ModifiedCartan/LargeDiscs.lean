import ModifiedCartan.Kobayashi

noncomputable section
set_option autoImplicit false
open Filter Topology Set
open scoped ENNReal
namespace ModifiedCartan

theorem exists_large_tangentDisc_of_metric_lt {N : ℕ} {Y : Set (Fin N → ℂ)}
    {x v : Fin N → ℂ} {R : ℝ} (hR : 0 < R)
    (hk : kobayashiRoyden Y x v < ENNReal.ofReal (1 / R)) :
    ∃ t : ℝ, R < t ∧ Nonempty (TangentDisc Y x v t) := by
  obtain ⟨c, ⟨t, ht, rfl, hdisc⟩, hc⟩ := sInf_lt_iff.mp hk
  have hlt : 1 / t < 1 / R := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hc
  have hRt : R < t := by simpa using (div_lt_div_iff₀ ht hR).mp hlt
  exact ⟨t, hRt, hdisc⟩

theorem large_tangentDisc_sequence_of_zero {N : ℕ} {Y : Set (Fin N → ℂ)}
    {x v : Fin N → ℂ} (hk : kobayashiRoyden Y x v = 0) :
    ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ Tendsto t atTop atTop ∧
      ∀ n, Nonempty (TangentDisc Y x v (t n)) := by
  have he : ∀ n : ℕ, ∃ t : ℝ, (n : ℝ) + 1 < t ∧ Nonempty (TangentDisc Y x v t) := by
    intro n
    apply exists_large_tangentDisc_of_metric_lt (by positivity)
    rw [hk]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  choose t ht hdisc using he
  refine ⟨t, fun n => lt_trans (by positivity) (ht n), ?_, hdisc⟩
  apply tendsto_atTop_mono (fun n => (ht n).le)
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

theorem metric_zero_of_large_tangentDiscs {N : ℕ} {Y : Set (Fin N → ℂ)}
    {x v : Fin N → ℂ} {t : ℕ → ℝ} (htpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop atTop) (hdisc : ∀ n, Nonempty (TangentDisc Y x v (t n))) :
    kobayashiRoyden Y x v = 0 := by
  have hlim : Tendsto (fun n => ENNReal.ofReal (1 / t n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_inv_atTop_zero.comp ht)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto' hlim
  intro n
  obtain ⟨F⟩ := hdisc n
  exact kobayashiRoyden_le_of_disc (htpos n) F

end ModifiedCartan
