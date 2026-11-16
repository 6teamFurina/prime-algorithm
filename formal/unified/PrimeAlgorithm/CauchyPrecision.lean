import PrimeAlgorithm.CauchyAnalytic
import PrimeAlgorithm.DoubleRamanujan

/-! An explicit linear number of Cauchy nodes gives the component accuracy
required for every input, including all small inputs. -/

noncomputable section
namespace PrimeAlgorithm.Cauchy

def primeNodes (b : ℕ) : ℕ := 5 * (7 * b + 23)

theorem primeNodes_pos (b : ℕ) : 0 < primeNodes b := by unfold primeNodes; omega

theorem primeNodes_decay (b : ℕ) :
    (6 / 7 : ℝ) ^ primeNodes b ≤ 1 / (2 : ℝ) ^ (7 * b + 23) := by
  unfold primeNodes
  rw [pow_mul]
  calc
    _ ≤ (1 / 2 : ℝ) ^ (7 * b + 23) :=
      pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ = _ := by rw [div_pow]; simp

theorem coefficient_accuracy (b : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hbound : 49 * H ≤ (2 : ℝ) ^ (b + 17)) :
    49 * H * (6 / 7 : ℝ) ^ primeNodes b ≤ DoubleRamanujan.componentTolerance b := by
  rw [DoubleRamanujan.componentTolerance_dyadic]
  calc
    _ ≤ (2 : ℝ) ^ (b + 17) * (1 / (2 : ℝ) ^ (7 * b + 23)) :=
      mul_le_mul hbound (primeNodes_decay b) (by positivity) (by positivity)
    _ = 1 / (2 : ℝ) ^ (6 * b + 6) := by
      rw [show 7 * b + 23 = (b + 17) + (6 * b + 6) by omega, pow_add]
      field_simp
      simp only [pow_add]

theorem log_coefficient_bound (b : ℕ) :
    49 * ((b : ℝ) + 6) ≤ (2 : ℝ) ^ (b + 17) := by
  have hb : (b : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast (Nat.lt_two_pow_self (n := b)).le
  have ht : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  nlinarith

theorem inverse_log_bound : (Real.log (5 / 4))⁻¹ ≤ (5 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  have hlo : (1 / 5 : ℝ) ≤ Real.log (5 / 4) := by norm_num at h; exact h
  have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 5) hlo
  norm_num at hi
  exact hi

theorem phase_exp_bound : Real.exp (7 * Real.pi / 4) ≤ (2187 : ℝ) := by
  calc
    _ ≤ Real.exp 7 := Real.exp_le_exp.2 (by nlinarith [Real.pi_lt_four])
    _ = (Real.exp 1) ^ 7 := by simpa using Real.exp_nat_mul 1 7
    _ ≤ (3 : ℝ) ^ 7 := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 7
    _ = _ := by norm_num

theorem log_approx_accuracy (b j : ℕ) (hj : j ≤ b)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖cauchyApprox (primeNodes b) (logAmplitude j) y - logAmplitude j y‖ ≤
      DoubleRamanujan.componentTolerance b := by
  apply (cauchyApprox_log_error (primeNodes_pos b) j hy).trans
  apply coefficient_accuracy b ((j : ℝ) + 6) (by positivity)
  have hjr : (j : ℝ) ≤ b := by exact_mod_cast hj
  exact (by linarith : 49 * ((j : ℝ) + 6) ≤ 49 * ((b : ℝ) + 6)).trans
    (log_coefficient_bound b)

theorem invLog_approx_accuracy (b j : ℕ) (hj : 1 ≤ j)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖cauchyApprox (primeNodes b) (invLogAmplitude j) y - invLogAmplitude j y‖ ≤
      DoubleRamanujan.componentTolerance b := by
  apply (cauchyApprox_invLog_error (primeNodes_pos b) hj hy).trans
  apply coefficient_accuracy b _ (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))
  have ht : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  nlinarith [inverse_log_bound]

theorem phase_approx_accuracy (b : ℕ) {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖cauchyApprox (primeNodes b) shiftedPhase y - shiftedPhase y‖ ≤
      DoubleRamanujan.componentTolerance b := by
  apply (cauchyApprox_phase_error (primeNodes_pos b) hy).trans
  apply coefficient_accuracy b _ (Real.exp_pos _).le
  have ht : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  nlinarith [phase_exp_bound]

end PrimeAlgorithm.Cauchy
