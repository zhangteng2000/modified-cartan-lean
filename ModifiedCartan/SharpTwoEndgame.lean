import ModifiedCartan.VaryingComposition
import ModifiedCartan.WronskianComposition
import ModifiedCartan.QuotientDerivativeDecay
import ModifiedCartan.ConvexZeroAvoidance
import ModifiedCartan.SegmentNeighborhood

noncomputable section
set_option autoImplicit false
open Filter Topology Complex Metric Set
namespace ModifiedCartan

/-- The fixed-domain contradiction uses the actual composed functions and
their Wronskians. Zeros of the sum limit are removed only inside the auxiliary
convex rectangle, whose zero-free part is proved preconnected. -/
theorem sharp_two_fixed_domain_contradiction {a : Fin 2 → ℕ → ℂ → ℂ} {s : ℂ → ℂ}
    {g : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {β T h : ℝ} {t : ℕ → ℝ}
    (ha : ∀ i n, DifferentiableOn ℂ (a i n) (disk 1))
    (hsum : CompactConvergence (fun n z => ∑ i, a i n z) s (disk 1))
    (hg : ∀ n, DifferentiableOn ℂ (g n) (disk 1))
    (hgmap : ∀ n, MapsTo (g n) (disk 1) (closedBall 0 β)) (hβ1 : β < 1)
    (hglim : CompactConvergence g G (disk 1))
    (hT : 0 ≤ T) (hh : 0 < h) (hrect1 : T + 2 * h < 1)
    (htlim : Tendsto t atTop (𝓝 T))
    (hleft : s (G ((-T : ℝ) : ℂ)) ≠ 0) (hright : s (G (T : ℂ)) ≠ 0)
    (hW : CompactConvergence (fun n z => wronskian (fun i => a i n) (g n z)) 0 (segmentRectangle T h))
    (hzero : Tendsto (fun n => a 0 n (g n ((-t n : ℝ) : ℂ)) /
      (∑ i, a i n (g n ((-t n : ℝ) : ℂ)))) atTop (𝓝 0))
    (hone : Tendsto (fun n => a 0 n (g n (t n : ℂ)) /
      (∑ i, a i n (g n (t n : ℂ)))) atTop (𝓝 1)) : False := by
  let b := fun i n z => a i n (g n z)
  let S := fun z => s (G z)
  let R := segmentRectangle T h
  let V : Set ℂ := {z | z ∈ R ∧ S z ≠ 0}
  have hR1 : R ⊆ disk 1 := fun z hz => by simpa [disk] using (segmentRectangle_norm hz).trans hrect1
  have hRr : R ⊆ closedBall 0 (T + 2 * h) := fun z hz => by
    simpa only [mem_closedBall, dist_zero_right] using (segmentRectangle_norm hz).le
  have hgunit : ∀ n, MapsTo (g n) (disk 1) (disk 1) := fun n z hz => closedBall_subset_ball hβ1 (hgmap n hz)
  have hGmap : MapsTo G (disk 1) (closedBall 0 β) := by
    intro z hz
    exact isClosed_closedBall.mem_of_tendsto (compactConvergence_pointwise hglim hz)
      (Eventually.of_forall (fun n => hgmap n hz))
  have hs := compactConvergence_holomorphic isOpen_ball hsum
    (fun n => DifferentiableOn.fun_sum (fun i _ => ha i n))
  have hsum' : CompactConvergence (fun n z => ∑ i, b i n z) S (disk 1) :=
    compactConvergence_comp_varying hsum hglim (isCompact_closedBall (0 : ℂ) β)
      (closedBall_subset_ball hβ1) (hs.continuousOn.mono (closedBall_subset_ball hβ1))
      (Eventually.of_forall hgmap) hGmap
  have hb : ∀ i n, DifferentiableOn ℂ (b i n) (disk 1) := fun i n => (ha i n).comp (hg n) (hgunit n)
  have hS := compactConvergence_holomorphic isOpen_ball hsum'
    (fun n => DifferentiableOn.fun_sum (fun i _ => hb i n))
  have hend := segmentRectangle_endpoints hT hh
  have hSne : ∃ z ∈ disk 1, S z ≠ 0 := ⟨((-T : ℝ) : ℂ), hR1 hend.1, hleft⟩
  have hVopen : IsOpen V := (hS.continuousOn.mono hR1).isOpen_inter_preimage
    (segmentRectangle_open T h) isOpen_compl_singleton
  have hVconn : IsPreconnected V := holomorphic_nonzero_convex_preconnected hS hSne
    (segmentRectangle_open T h) (segmentRectangle_convex T h) (by positivity) hrect1 hRr
  have hV1 : V ⊆ disk 1 := fun z hz => hR1 hz.1
  have hWR : CompactConvergence (fun n => wronskian (fun i => b i n)) 0 R :=
    compactConvergence_wronskian_comp_zero isOpen_ball (segmentRectangle_open T h) ha
      (fun n => (hg n).mono hR1) (fun n z hz => hgunit n (hR1 hz))
      (compactConvergence_mono hglim hR1) hW
  have hWlim : CompactConvergence (fun n => wronskian (fun i => b i n)) 0 V :=
    compactConvergence_mono hWR (fun _ hz => hz.1)
  have hder := two_term_quotient_vanishingDerivative hV1 hb hsum' (fun _ hz => hz.2) hWlim
  have htC : Tendsto (fun n => (t n : ℂ)) atTop (𝓝 (T : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp htlim
  have hntC : Tendsto (fun n => ((-t n : ℝ) : ℂ)) atTop (𝓝 ((-T : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_neg] using htC.neg
  exact vanishingDerivative_endpoint_contradiction hder hVopen hVconn
    ⟨hend.1, hleft⟩ ⟨hend.2, hright⟩ hntC htC hzero hone

end ModifiedCartan
