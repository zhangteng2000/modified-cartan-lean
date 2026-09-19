import ModifiedCartan.ZeroFreeAnnulus
import ModifiedCartan.Hurwitz

noncomputable section
set_option autoImplicit false
open Set Filter Topology Metric
namespace ModifiedCartan

def complexAnnulus (a b : ℝ) : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b}

/-- A finite quotient limit other than minus one allows its two functions to
be merged on a surrounding annulus. The actual merged unit and all ratios
needed to lift C classes are constructed after a finite shift. -/
theorem pair_merge_on_annulus {g h : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ n, IsHolomorphicUnit (g n) (disk 1))
    (hh : ∀ n, IsHolomorphicUnit (h n) (disk 1))
    (hlim : CompactConvergence (fun n z => g n z / h n z) F (disk 1))
    (hFne : ∃ z ∈ disk 1, F z ≠ -1) :
    ∃ α β : ℝ, r < α ∧ α < β ∧ β < 1 ∧ ∃ N : ℕ,
      (∀ n, IsHolomorphicUnit (fun z => g (N+n) z + h (N+n) z) (complexAnnulus α β)) ∧
      LocallyBounded (fun n z => g (N+n) z / (g (N+n) z + h (N+n) z)) (complexAnnulus α β) ∧
      LocallyBounded (fun n z => h (N+n) z / (g (N+n) z + h (N+n) z)) (complexAnnulus α β) ∧
      LocallyBounded (fun n z => (g (N+n) z + h (N+n) z) / h (N+n) z) (complexAnnulus α β) := by
  have hFd := compactConvergence_holomorphic isOpen_ball hlim
    (fun n => (hg n).1.div (hh n).1 (hh n).2)
  have hFnz : ∃ z ∈ disk 1, F z + 1 ≠ 0 := by
    obtain ⟨z, hz, hn⟩ := hFne
    exact ⟨z, hz, fun he => hn (by linear_combination he)⟩
  obtain ⟨α, β, hrα, hαβ, hβ, hnz⟩ := exists_zero_free_annulus (hFd.add (differentiableOn_const 1)) hFnz
    hr (show r < (r+1)/2 by linarith) (show (r+1)/2 < 1 by linarith)
  have hβ1 : β < 1 := by linarith
  let K : Set ℂ := {z | α ≤ ‖z‖ ∧ ‖z‖ ≤ β}
  have hK : IsCompact K := by
    have hc : IsCompact (closedBall (0 : ℂ) β ∩ {z : ℂ | α ≤ ‖z‖}) :=
      (isCompact_closedBall (0 : ℂ) β).inter_right (isClosed_le continuous_const continuous_norm)
    convert! hc using 1
    ext z
    simp [K, and_comm]
  have hKU : K ⊆ disk 1 := by
    intro z hz
    simpa [disk] using hz.2.trans_lt hβ1
  have hVK : complexAnnulus α β ⊆ K := fun _ hz => ⟨hz.1.le, hz.2.le⟩
  have hVU := hVK.trans hKU
  let q : ℕ → ℂ → ℂ := fun n z => g n z / h n z + 1
  have hqconv : CompactConvergence q (fun z => F z + 1) (disk 1) := by
    intro L hLU hL
    simpa only [Pi.add_def] using (hlim L hLU hL).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).tendstoUniformlyOn_const L)
  obtain ⟨c, hc, hclower⟩ := compactConvergence_eventually_lower_bound hqconv hKU hK
    ((hFd.continuousOn.add continuousOn_const).mono hKU) (fun z hz => hnz z hz.1 hz.2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hclower
  have hlower : ∀ n z, z ∈ complexAnnulus α β → c ≤ ‖q (N+n) z‖ :=
    fun n z hz => hN (N+n) (by omega) z (hVK hz)
  have hqid : ∀ n z, z ∈ complexAnnulus α β →
      q (N+n) z * h (N+n) z = g (N+n) z + h (N+n) z := by
    intro n z hz
    dsimp [q]
    field_simp [(hh (N+n)).2 z (hVU hz)]
  have hqunit : ∀ n z, z ∈ complexAnnulus α β → q (N+n) z ≠ 0 :=
    fun n z hz => norm_pos_iff.mp (hc.trans_le (hlower n z hz))
  have hmerged : ∀ n, IsHolomorphicUnit
      (fun z => g (N+n) z + h (N+n) z) (complexAnnulus α β) := by
    intro n
    refine ⟨((hg (N+n)).1.add (hh (N+n)).1).mono hVU, ?_⟩
    intro z hz
    change g (N+n) z + h (N+n) z ≠ 0
    rw [← hqid n z hz]
    exact mul_ne_zero (hqunit n z hz) ((hh (N+n)).2 z (hVU hz))
  have hinv : LocallyBounded (fun n z => (q (N+n) z)⁻¹) (complexAnnulus α β) := by
    intro L hLV _
    refine ⟨c⁻¹, ?_⟩
    intro n z hz
    rw [norm_inv]
    exact (inv_le_inv₀ (hc.trans_le (hlower n z (hLV hz))) hc).mpr (hlower n z (hLV hz))
  have hright : LocallyBounded
      (fun n z => h (N+n) z / (g (N+n) z + h (N+n) z)) (complexAnnulus α β) := by
    apply locallyBounded_congr hinv
    intro n z hz
    rw [← hqid n z hz]
    field_simp [(hh (N+n)).2 z (hVU hz)]
  have hratio := locallyBounded_mono (locallyBounded_subsequence
    (compactConvergence_locallyBounded hlim
      (fun n => ((hg n).1.div (hh n).1 (hh n).2).continuousOn)) (fun n => N+n)) hVU
  have hleft := quotient_bounded_trans (fun n z hz => (hh (N+n)).2 z (hVU hz)) hratio hright
  have hqb := locallyBounded_mono (locallyBounded_subsequence
    (compactConvergence_locallyBounded hqconv
      (fun n => (((hg n).1.div (hh n).1 (hh n).2).add (differentiableOn_const 1)).continuousOn))
      (fun n => N+n)) hVU
  have hback : LocallyBounded
      (fun n z => (g (N+n) z + h (N+n) z) / h (N+n) z) (complexAnnulus α β) := by
    apply locallyBounded_congr hqb
    intro n z hz
    dsimp [q]
    rw [add_div, div_self ((hh (N+n)).2 z (hVU hz))]
  exact ⟨α, β, hrα, hαβ, hβ1, N, hmerged, hleft, hright, hback⟩

end ModifiedCartan
