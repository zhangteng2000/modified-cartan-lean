import ModifiedCartan.PoissonExtension
import ModifiedCartan.Basic
import Mathlib.Topology.Order.Lattice

noncomputable section
set_option autoImplicit false
open Complex InnerProductSpace Metric Real Set
namespace ModifiedCartan

def maxWithZero {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Option ι => i.elim 0 u)

theorem maxWithZero_nonneg {ι : Type*} [Fintype ι] (u : ι → ℝ) : 0 ≤ maxWithZero u :=
  Finset.le_sup' (fun i : Option ι => i.elim 0 u) (Finset.mem_univ none)

theorem le_maxWithZero {ι : Type*} [Fintype ι] (u : ι → ℝ) (i : ι) : u i ≤ maxWithZero u :=
  Finset.le_sup' (fun i : Option ι => i.elim 0 u) (Finset.mem_univ (some i))

theorem maxWithZero_le {ι : Type*} [Fintype ι] {u : ι → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hu : ∀ i, u i ≤ b) : maxWithZero u ≤ b := by
  apply Finset.sup'_le
  intro i _
  cases i with
  | none => exact hb
  | some i => exact hu i

theorem continuousOn_maxWithZero {ι : Type*} [Fintype ι] {u : ι → ℂ → ℝ} {U : Set ℂ}
    (hu : ∀ i, ContinuousOn (u i) U) : ContinuousOn (fun z => maxWithZero (fun i => u i z)) U := by
  unfold maxWithZero
  apply ContinuousOn.finset_sup'_apply
  intro i _
  cases i with
  | none => exact continuousOn_const
  | some i => exact hu i

def harmonicGrowthMean {ι : Type*} [Fintype ι] (u : ι → ℂ → ℝ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z => maxWithZero (fun i => u i z)) 0 r

theorem harmonicGrowthMean_nonneg {ι : Type*} [Fintype ι] (u : ι → ℂ → ℝ) (r : ℝ) :
    0 ≤ harmonicGrowthMean u r :=
  Real.circleAverage_nonneg_of_nonneg (fun _ _ => maxWithZero_nonneg _)

theorem harmonic_max_le_poissonExtension {ι : Type*} [Fintype ι] {u : ι → ℂ → ℝ} {R : ℝ}
    (hR : 0 < R) (hu : ∀ i, HarmonicOnNhd (u i) (closedBall (0 : ℂ) R))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    maxWithZero (fun i => u i w) ≤ poissonExtension (fun z => maxWithZero (fun i => u i z)) R w := by
  let v := fun z => maxWithZero (fun i => u i z)
  have hv : CircleIntegrable v 0 R := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hR]
    exact (continuousOn_maxWithZero (fun i => (hu i).continuousOn)).mono sphere_subset_closedBall
  apply maxWithZero_le
  · have hh := poissonExtension_mono (circleIntegrable_const (0:ℝ) 0 R) hv
      (fun z _ => maxWithZero_nonneg _) hw
    simpa [poissonExtension, Real.circleAverage_const, v] using hh
  · intro i
    apply harmonic_le_poissonExtension _ hv (fun z _ => le_maxWithZero _ i) hw
    apply (hu i).mono _ |>.harmonicContOnCl
    rw [closure_ball (0 : ℂ) hR.ne']

theorem harmonicGrowthMean_le {ι : Type*} [Fintype ι] {u : ι → ℂ → ℝ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R)
    (hu : ∀ i, HarmonicOnNhd (u i) (closedBall (0 : ℂ) R)) :
    harmonicGrowthMean u r ≤ harmonicGrowthMean u R := by
  obtain rfl | hrR' := hrR.eq_or_lt
  · exact le_rfl
  have hR : 0 < R := hr.trans_lt hrR'
  let v := fun z => maxWithZero (fun i => u i z)
  have hvcont : ContinuousOn v (closedBall (0 : ℂ) R) :=
    continuousOn_maxWithZero (fun i => (hu i).continuousOn)
  have hvR : CircleIntegrable v 0 R := by
    apply ContinuousOn.circleIntegrable'
    simpa [abs_of_pos hR] using hvcont.mono sphere_subset_closedBall
  have hvr : CircleIntegrable v 0 r := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_nonneg hr]
    exact hvcont.mono (sphere_subset_closedBall.trans (closedBall_subset_closedBall hrR'.le))
  have hP := (poissonExtension_harmonic hvR).mono (closedBall_subset_ball hrR')
  have hPi : CircleIntegrable (poissonExtension v R) 0 r := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_nonneg hr]
    exact hP.continuousOn.mono sphere_subset_closedBall
  have hmean := Real.circleAverage_mono hvr hPi (fun z hz =>
    harmonic_max_le_poissonExtension hR hu (by
      apply closedBall_subset_ball hrR'
      simpa [abs_of_nonneg hr] using sphere_subset_closedBall hz))
  have he : Real.circleAverage (poissonExtension v R) 0 r = poissonExtension v R 0 :=
    InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by simpa [abs_of_nonneg hr] using hP)
  rwa [he, poissonExtension_zero hR hvR] at hmean

theorem harmonicGrowthMean_monotoneOn {ι : Type*} [Fintype ι] {u : ι → ℂ → ℝ} {T : ℝ}
    (hu : ∀ i, HarmonicOnNhd (u i) (ball (0 : ℂ) T)) :
    MonotoneOn (harmonicGrowthMean u) (Ico 0 T) := by
  intro r hr R hR hrR
  exact harmonicGrowthMean_le hr.1 hrR
    (fun i => (hu i).mono (closedBall_subset_ball hR.2))

theorem harmonicGrowthMean_continuousOn {ι : Type*} [Fintype ι] {u : ι → ℂ → ℝ} {T : ℝ}
    (hu : ∀ i, HarmonicOnNhd (u i) (ball (0 : ℂ) T)) :
    ContinuousOn (harmonicGrowthMean u) (Ico 0 T) := by
  apply ContinuousOn.circleAverage _ (fun r hr => hr.1)
  apply (continuousOn_maxWithZero (fun i => (hu i).continuousOn)).mono
  intro z hz
  exact mem_ball_iff_norm.mpr hz.2

end ModifiedCartan
