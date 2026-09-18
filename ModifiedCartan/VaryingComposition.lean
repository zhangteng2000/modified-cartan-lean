import ModifiedCartan.Convergence
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
set_option autoImplicit false
open Filter Topology Metric Set
namespace ModifiedCartan

theorem uniformOn_comp_varying {f g : ℕ → ℂ → ℂ} {F G : ℂ → ℂ} {K L : Set ℂ}
    (hf : TendstoUniformlyOn f F atTop L) (hg : TendstoUniformlyOn g G atTop K)
    (hF : UniformContinuousOn F L) (hgL : ∀ᶠ n in atTop, MapsTo (g n) K L)
    (hGL : MapsTo G K L) :
    TendstoUniformlyOn (fun n z => f n (g n z)) (fun z => F (G z)) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp hF (ε / 2) (half_pos hε)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf (ε / 2) (half_pos hε),
    Metric.tendstoUniformlyOn_iff.mp hg δ hδ, hgL] with n hfn hgn hgnL
  intro z hz
  have h₁ := hδF (G z) (hGL hz) (g n z) (hgnL hz) (hgn z hz)
  have h₂ := hfn (g n z) (hgnL hz)
  exact (dist_triangle (F (G z)) (F (g n z)) (f n (g n z))).trans_lt (by linarith)

theorem compactConvergence_comp_varying {f g : ℕ → ℂ → ℂ} {F G : ℂ → ℂ} {U V L : Set ℂ}
    (hf : CompactConvergence f F V) (hg : CompactConvergence g G U)
    (hL : IsCompact L) (hLV : L ⊆ V) (hF : ContinuousOn F L)
    (hgL : ∀ᶠ n in atTop, MapsTo (g n) U L) (hGL : MapsTo G U L) :
    CompactConvergence (fun n z => f n (g n z)) (fun z => F (G z)) U := by
  intro K hKU hK
  exact uniformOn_comp_varying (hf L hLV hL) (hg K hKU hK) (hL.uniformContinuousOn_of_continuous hF)
    (hgL.mono (fun n hn z hz => hn (hKU hz))) (fun z hz => hGL (hKU hz))

end ModifiedCartan
