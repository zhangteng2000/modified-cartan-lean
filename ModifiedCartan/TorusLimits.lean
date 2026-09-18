import ModifiedCartan.PartitionJets
import ModifiedCartan.LaurentJets
import ModifiedCartan.Kobayashi

noncomputable section
set_option autoImplicit false
open Filter Topology Set Metric
namespace ModifiedCartan

/-- The full analytic limiting-disc argument, allowing centers and tangent vectors
to vary. The Laurent polynomial has its actual finite nonzero support presentation. -/
theorem laurent_orbit_zero_of_large_discs {N q : ℕ} (P : LaurentData N q)
    (hcoeff : ∀ i, P.coefficient i ≠ 0)
    (F : ℕ → ℂ → Fin N → ℂ) (xn vn : ℕ → Fin N → ℂ) (t : ℕ → ℝ)
    (x v : Fin N → ℂ) (hx : ∀ j, x j ≠ 0)
    (hxlim : Tendsto xn atTop (𝓝 x)) (hvlim : Tendsto vn atTop (𝓝 v))
    (ht : Tendsto t atTop atTop) (htpos : ∀ n, 0 < t n)
    (hF : ∀ j n, IsHolomorphicUnit (fun z => F n z j) (disk 1))
    (hcenter : ∀ n, F n 0 = xn n)
    (hder : ∀ j n, HasDerivAt (fun z => F n z j) ((t n : ℂ) * vn n j) 0)
    (hzero : ∀ n z, z ∈ disk 1 → P.eval (F n z) = 0) :
    ∀ z : ℂ, P.eval (exponentialOrbit x v z) = 0 := by
  let f : Family q := fun i n z => P.coefficient i * laurentMonomial (P.exponent i) (F n z)
  have hunit : UnitFamily f := by
    intro i n
    have hm := laurentMonomial_holomorphicUnit (P.exponent i) (fun j => hF j n)
    exact ⟨hm.1.const_mul _, fun z hz => mul_ne_zero (hcoeff i) (hm.2 z hz)⟩
  have hsum : ZeroSum f := fun n z hz => hzero n z hz
  have hc : ∀ i, P.orbitCoefficient x i ≠ 0 := fun i =>
    mul_ne_zero (hcoeff i) (laurentMonomial_ne_zero (P.exponent i) hx)
  have hxn : ∀ n j, xn n j ≠ 0 := by
    intro n j
    rw [← hcenter n]
    exact (hF j n).2 0 (by simp [disk])
  have hval : ∀ i, Tendsto (fun n => f i n 0) atTop (𝓝 (P.orbitCoefficient x i)) := by
    intro i
    have he : (fun n => f i n 0) = fun n => P.orbitCoefficient (xn n) i := by
      funext n
      dsimp [f, LaurentData.orbitCoefficient]
      rw [hcenter n]
    rw [he]
    exact laurent_orbitCoefficient_tendsto P hx hxlim i
  have hjet : ∀ i, Tendsto (fun n => deriv (f i n) 0 / (t n : ℂ)) atTop
      (𝓝 (P.orbitCoefficient x i * P.orbitRate x v i)) := by
    intro i
    have he : ∀ n, deriv (f i n) 0 / (t n : ℂ) =
        P.orbitCoefficient (xn n) i * P.orbitRate (xn n) (vn n) i := by
      intro n
      have hh := (laurent_term_hasDerivAt_scaled P i (hxn n) (hcenter n) (fun j => hder j n)).deriv
      change deriv (fun z => P.coefficient i * laurentMonomial (P.exponent i) (F n z)) 0 / (t n : ℂ) = _
      rw [hh]
      field_simp [Complex.ofReal_ne_zero.mpr (htpos n).ne']
    simp only [he]
    exact (laurent_orbitCoefficient_tendsto P hx hxlim i).mul (laurent_orbitRate_tendsto P hx hxlim hvlim i)
  intro z
  rw [laurent_eval_on_orbit]
  exact exponentialSum_zero_of_unit_jet_limits hunit hsum ht htpos
    (P.orbitCoefficient x) (P.orbitRate x v) hc hval hjet z

end ModifiedCartan
