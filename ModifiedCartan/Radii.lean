import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace ModifiedCartan

def sharpRadius : ℝ := 2 - Real.sqrt 3

theorem sharpRadius_pos : 0 < sharpRadius := by
  unfold sharpRadius
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonneg := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem sharpRadius_lt_one : sharpRadius < 1 := by
  unfold sharpRadius
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonneg := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem sharpRadius_quadratic : 1 + sharpRadius ^ 2 = 4 * sharpRadius := by
  unfold sharpRadius
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem sharpRadius_ratio : (1 + sharpRadius) / (1 - sharpRadius) = Real.sqrt 3 := by
  have h := sharpRadius_lt_one
  rw [div_eq_iff (by linarith : 1 - sharpRadius ≠ 0)]
  unfold sharpRadius
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- The formula 4 arctanh(r) = 2 log((1+r)/(1-r)) at r = 2-sqrt(3). -/
theorem sharpRadius_log_diameter :
    2 * Real.log ((1 + sharpRadius) / (1 - sharpRadius)) = Real.log 3 := by
  rw [sharpRadius_ratio, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

def eta (K : ℕ → ℝ) (m : ℕ) : ℝ := 1 / (1024 * (K m + m))

/-- Index zero is unused in the paper and is set to one. -/
def absorptionRadius (K : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => sharpRadius
  | n + 3 => eta K (n + 3) * absorptionRadius K (n + 2)

theorem eta_pos {K : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m) (hK : (m : ℝ) ≤ K m) :
    0 < eta K m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold eta
  exact div_pos (by norm_num) (by linarith)

theorem eta_le_one {K : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m) (hK : (m : ℝ) ≤ K m) :
    eta K m ≤ 1 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold eta
  apply (div_le_iff₀ (by linarith : 0 < 1024 * (K m + m))).mpr
  nlinarith

theorem absorptionRadius_pos {K : ℕ → ℝ} (hK : ∀ m : ℕ, (m : ℝ) ≤ K m) :
    ∀ m, 0 < absorptionRadius K m
  | 0 => by simp [absorptionRadius]
  | 1 => by simp [absorptionRadius]
  | 2 => sharpRadius_pos
  | n + 3 => mul_pos (eta_pos (by omega) (hK _)) (absorptionRadius_pos hK (n + 2))

theorem absorptionRadius_step {K : ℕ → ℝ} (hK : ∀ m : ℕ, (m : ℝ) ≤ K m) :
    ∀ m, absorptionRadius K (m + 1) ≤ absorptionRadius K m
  | 0 => by simp [absorptionRadius]
  | 1 => le_of_lt sharpRadius_lt_one
  | 2 => by
    change eta K 3 * sharpRadius ≤ sharpRadius
    exact mul_le_of_le_one_left (le_of_lt sharpRadius_pos) (eta_le_one (by omega) (hK 3))
  | n + 3 => by
    change eta K (n + 4) * absorptionRadius K (n + 3) ≤ absorptionRadius K (n + 3)
    exact mul_le_of_le_one_left (le_of_lt (absorptionRadius_pos hK _))
      (eta_le_one (by omega) (hK _))

theorem absorptionRadius_antitone {K : ℕ → ℝ} (hK : ∀ m : ℕ, (m : ℝ) ≤ K m) :
    Antitone (absorptionRadius K) := antitone_nat_of_succ_le (absorptionRadius_step hK)

theorem absorption_constant_bound {K m δ : ℝ} (hm : 0 < m) (hK : m ≤ K)
    (hδ : δ ≤ 1 / (1024 * (K + m))) :
    8 * m * δ + (128 * K + 20 * m) / (1024 * (K + m)) ≤ 1 / 8 := by
  have hd : 0 < 1024 * (K + m) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 8 * m)
  calc
    _ ≤ 8 * m * (1 / (1024 * (K + m))) +
        (128 * K + 20 * m) / (1024 * (K + m)) := by linarith
    _ = (128 * K + 28 * m) / (1024 * (K + m)) := by ring
    _ ≤ 1 / 8 := by apply (div_le_iff₀ hd).mpr; linarith

end ModifiedCartan
