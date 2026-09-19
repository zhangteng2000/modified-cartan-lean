import ModifiedCartan.CartanRadialCases
import ModifiedCartan.CartanPairSelection
import ModifiedCartan.OrientedWronskianGrowth
import ModifiedCartan.RadialWronskianNonzero
import ModifiedCartan.QuotientAnchors

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real MeasureTheory
namespace ModifiedCartan

def tripleIndexEmbedding {p : ℕ} (i j k : Fin p) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Fin 3 ↪ Fin p where
  toFun := ![i,j,k]
  inj' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all

/-- All injective triples simultaneously acquire actual anchors after a
single finite shift. The upper-growth input can come from a larger family. -/
theorem eventually_uniform_triple_anchors {p : ℕ} {f : Family p} {L b c T R r₀ η A : ℝ}
    (hL : 0 < L) (hLb : L < b) (hbc : b < c) (hcT : c < T)
    (hTR : T < R) (hRr : R < r₀) (hr1 : r₀ < 1)
    (hη : 0 < η) (hηL : η < L) (hA : 0 ≤ A) (hf : UnitFamily f)
    (hno : NoVanishingQuotientSubsequence f (disk L))
    (hfinite : OnlyNegativeOneUnitLimits f (disk L))
    (hanchors : ∀ n i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i n w/f j n w ≠ 0 ∧
      -A ≤ Real.log ‖f i n w/f j n w‖)
    (hWanchors : ∀ n i j, i ≠ j → ∃ w : ℂ, ‖w‖ ≤ L ∧
      1 ≤ ‖normalizedWronskian ![f i n,f j n] w‖) :
    ∃ D C : ℝ, 0 ≤ D ∧ 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ v : Fin 3 ↪ Fin p,
      (∃ w : ℂ, ‖w‖ ≤ c ∧ normalizedWronskian (fun j => f (v j) n) w ≠ 0) ∧
      ∀ r s M : ℝ, r₀ ≤ r → r < s → s < 1 → 1 ≤ M → s-r = 1/M →
        (∀ i j, proximityMean (fun z => f i n z/f j n z) s ≤ 2*M) →
        (∃ w : ℂ, ‖w‖ ≤ c ∧ normalizedWronskian (fun j => f (v j) n) w ≠ 0 ∧
          -D*(Real.log M+1) ≤ Real.log ‖normalizedWronskian (fun j => f (v j) n) w‖) ∧
        proximityMean (fun z => (normalizedWronskian (fun j => f (v j) n) z)⁻¹) r ≤
          C*(Real.log M+1) := by
  have hLr : L < r₀ := hLb.trans (hbc.trans (hcT.trans (hTR.trans hRr)))
  have he (v : Fin 3 ↪ Fin p) := eventually_small_third_good_set hη hL.le
    (hηL.trans hLb) hLb hbc (hcT.trans (hTR.trans (hRr.trans hr1))) hA hL hLb.le
    (fun i n => hf (v i) n) (noVanishingQuotientSubsequence_reindex hno v)
    (onlyNegativeOneUnitLimits_reindex hfinite v.injective)
    (fun n i j => hanchors n (v i) (v j))
    (fun n i j hij => hWanchors n (v i) (v j) (v.injective.ne hij))
  have hall := eventually_all.mpr he
  obtain ⟨D,C,hD,hC,hbound⟩ := wronskian_three_growth_of_small_good_set hL (hL.trans hLb).le
    hbc (hLb.trans (hbc.trans hcT)) hcT hTR hRr hr1 hη (hηL.trans hLr) (Real.exp_pos (-A))
  refine ⟨D,C,hD,hC,?_⟩
  filter_upwards [hall] with n hn
  intro v
  refine ⟨normalizedWronskian_three_nonzero_of_small_good_set hbc
    (hcT.trans (hTR.trans (hRr.trans hr1))) (fun j => hf (v j) n) (hn v),?_⟩
  intro r s M hr hrs hs hM hgap hmeans
  apply hbound (fun j => f (v j) n) r s M (fun j => hf (v j) n) hr hrs hs hM hgap
  · intro i j
    exact diskSupNorm_ge_exp_of_log_anchor (hηL.trans (hLr.trans hr1))
      (unit_quotient (hf (v i) n) (hf (v j) n)) (hanchors n (v i) (v j))
  · exact fun i j => hmeans (v i) (v j)
  · exact fun i j hij => hWanchors n (v i) (v j) (v.injective.ne hij)
  · exact hn v

end ModifiedCartan
