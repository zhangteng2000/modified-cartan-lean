import ModifiedCartan.UnitSumWronskian
import ModifiedCartan.BoundaryErrorGrowth
import ModifiedCartan.QuotientAnchors
import ModifiedCartan.UniformReciprocalProximity
import ModifiedCartan.WronskianCommonFactor
import ModifiedCartan.WronskianQuotients

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric Real
namespace ModifiedCartan

/-- The final analytic closure in Cartan's argument: a logarithmic inverse
Wronskian estimate forces the same bound for the growth of all pairwise
quotients of the original zero-sum units. -/
theorem zero_sum_pairGrowth_bound_of_inverseWronskian {η r₀ A D : ℝ}
    (hη : 0 < η) (hηr : η < r₀) (hr1 : r₀ < 1) (hA : 0 ≤ A) (hD : 0 ≤ D) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fin (m+1) → ℂ → ℂ) (r s M : ℝ),
      (∀ i, IsHolomorphicUnit (f i) (disk 1)) → (∀ z ∈ disk 1, ∑ i, f i z = 0) →
      r₀ ≤ r → r < s → s < 1 → 1 ≤ M → s-r = 1/M → pairGrowthMean f s ≤ 2*M →
      (∀ i j, ∃ w : ℂ, ‖w‖ ≤ η ∧ f i w/f j w ≠ 0 ∧ -A ≤ Real.log ‖f i w/f j w‖) →
      (∃ w ∈ disk 1, normalizedWronskian (fun j : Fin m => f j.castSucc) w ≠ 0) →
      proximityMean (fun z => (normalizedWronskian (fun j : Fin m => f j.castSucc) z)⁻¹) r ≤ D*(Real.log M+1) →
      pairGrowthMean f r ≤ C*(Real.log M+1) := by
  obtain ⟨B,hB,herr⟩ := wronskianBoundaryError_growth_bound hη hηr (Real.exp_pos (-A)) m
  let E := D+B
  have hE : 0 ≤ E := add_nonneg hD hB
  obtain ⟨V,hV,hinv⟩ := proximityMean_inv_growth_bound hη.le hηr hA hE
  let C := 1+((m+1 : ℕ) : ℝ)*((m+1 : ℕ) : ℝ)*(E+V)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro f r s M hf hsum hr hrs hs hM hgap hMs ha hN hNm
  let q : Fin (m+1) → ℂ → ℂ := fun i z => f i z/f (Fin.last m) z
  let g : Fin m → ℂ → ℂ := fun j => q j.castSucc
  let N := normalizedWronskian (fun j : Fin m => f j.castSucc)
  let ℓ := Real.log M+1
  have hℓ : 1 ≤ ℓ := by dsimp [ℓ]; linarith [Real.log_nonneg hM]
  have hr0 : 0 < r := hη.trans (hηr.trans_le hr)
  have hr' : r < 1 := hrs.trans hs
  have hqu : ∀ i, IsHolomorphicUnit (q i) (disk 1) := fun i => unit_quotient (hf i) (hf (Fin.last m))
  have hgu : ∀ j, IsHolomorphicUnit (g j) (disk 1) := fun j => hqu j.castSucc
  have hnorm : EqOn (normalizedWronskian g) N (disk 1) := by
    intro z hz
    exact normalizedWronskian_common_divisor
      (fun j => (hf j.castSucc).1.analyticOnNhd isOpen_ball z hz)
      ((hf (Fin.last m)).1.analyticOnNhd isOpen_ball z hz) ((hf (Fin.last m)).2 z hz)
  have hWg : ∃ w ∈ disk 1, wronskian g w ≠ 0 := by
    obtain ⟨w,hw,hn⟩ := hN
    refine ⟨w,hw,?_⟩
    intro hh
    have hzero : normalizedWronskian g w = 0 := by rw [normalizedWronskian,hh,zero_div]
    rw [hnorm hw] at hzero
    exact hn hzero
  have hgsum : ∀ z ∈ disk 1, ∑ j, g j z = -1 := by
    intro z hz
    have hh := hsum z hz
    rw [Fin.sum_univ_castSucc] at hh
    change (∑ j : Fin m, f j.castSucc z/f (Fin.last m) z) = -1
    rw [← Finset.sum_div]
    apply (div_eq_iff ((hf (Fin.last m)).2 z hz)).mpr
    linear_combination hh
  have hgmean : ∀ j, proximityMean (g j) s ≤ 2*M := fun j =>
    (quotient_proximity_le_pairGrowthMean f j.castSucc (Fin.last m) s).trans hMs
  have hsup : ∀ j, Real.exp (-A) ≤ diskSupNorm (g j) η := fun j =>
    diskSupNorm_ge_exp_of_log_anchor (hηr.trans hr1) (hgu j) (ha j.castSucc (Fin.last m))
  have herror := herr g r s M (fun j => (hgu j).1) hsup hr hrs hs hM hgap hgmean
  have hsub : sphere (0 : ℂ) |r| ⊆ disk 1 := by
    rw [abs_of_pos hr0]
    exact sphere_subset_ball hr'
  have heinv : proximityMean (fun z => (normalizedWronskian g z)⁻¹) r =
      proximityMean (fun z => (N z)⁻¹) r :=
    proximityMean_congr_circle (fun z hz => congrArg Inv.inv (hnorm (hsub hz)))
  have hqm : ∀ i, proximityMean (q i) r ≤ E*ℓ := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have he : EqOn (q (Fin.last m)) (fun _ => 1) (sphere (0 : ℂ) |r|) := by
        intro z hz
        exact div_self ((hf (Fin.last m)).2 z (hsub hz))
      rw [proximityMean_congr_circle he]
      simpa [proximityMean,ValueDistribution.proximity_const] using mul_nonneg hE (by linarith : 0 ≤ ℓ)
    · have hc := constant_sum_proximity_le_normalizedWronskian_inv hr0 hr' hgu hgsum hWg j
      rw [heinv] at hc
      change proximityMean (q j.castSucc) r ≤ E*ℓ
      change proximityMean (fun z => (N z)⁻¹) r ≤ D*ℓ at hNm
      change Real.circleAverage (wronskianBoundaryError g 0) 0 r ≤ B*ℓ at herror
      change proximityMean (q j.castSucc) r ≤ proximityMean (fun z => (N z)⁻¹) r+_ at hc
      dsimp [E]
      nlinarith
  have hqinv : ∀ i, proximityMean (fun z => (q i z)⁻¹) r ≤ V*ℓ := by
    intro i
    apply hinv (q i) r M hr hr'.le hM
      ((hqu i).1.analyticOnNhd isOpen_ball |>.mono (closedBall_subset_ball hr')) (hqm i)
    obtain ⟨w,hw,hn,hl⟩ := ha i (Fin.last m)
    exact ⟨w,hw,hn,by change -A*ℓ ≤ Real.log ‖f i w/f (Fin.last m) w‖; nlinarith⟩
  have hpairs : ∀ i j, proximityMean (fun z => f i z/f j z) r ≤ (E+V)*ℓ := by
    intro i j
    have he : EqOn (fun z => f i z/f j z) (fun z => q i z/q j z) (sphere (0 : ℂ) |r|) := by
      intro z hz
      dsimp [q]
      field_simp [(hf (Fin.last m)).2 z (hsub hz)]
    rw [proximityMean_congr_circle he]
    have hh := proximityMean_div_le
      ((hqu i).1.analyticOnNhd isOpen_ball |>.mono hsub).meromorphicOn
      ((hqu j).1.analyticOnNhd isOpen_ball |>.mono hsub).meromorphicOn
    exact hh.trans ((add_le_add (hqm i) (hqinv j)).trans_eq (by ring))
  have hsumPairs : (∑ i, ∑ j, proximityMean (fun z => f i z/f j z) r) ≤
      ((m+1 : ℕ) : ℝ)*((m+1 : ℕ) : ℝ)*(E+V)*ℓ := by
    calc
      _ ≤ ∑ _i : Fin (m+1), ∑ _j : Fin (m+1), (E+V)*ℓ :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpairs i j))
      _ = _ := by simp [mul_assoc]
  change 1+(∑ i, ∑ j, proximityMean (fun z => f i z/f j z) r) ≤ C*ℓ
  dsimp [C]
  nlinarith

end ModifiedCartan
