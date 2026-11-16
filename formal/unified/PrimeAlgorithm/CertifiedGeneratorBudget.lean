import PrimeAlgorithm.CertifiedGenerator

set_option maxHeartbeats 1000000

noncomputable section
namespace PrimeAlgorithm.CertifiedGenerator
open CertifiedCauchy

/-- The Taylor and pi approximation precision used by the executable generator. -/
def eta (b : ℕ) : ℝ := (1/2:ℝ)^order b
/-- A shared error budget after the fixed analytic stability constants. -/
def epsilon (b : ℕ) : ℝ := 2^128*eta b

theorem eta_nonneg (b : ℕ) : 0≤eta b := by unfold eta; positivity
theorem eta_pos (b : ℕ) : 0<eta b := by unfold eta; positivity
theorem epsilon_nonneg (b : ℕ) : 0≤epsilon b := by unfold epsilon eta; positivity
theorem epsilon_pos (b : ℕ) : 0<epsilon b := by unfold epsilon eta; positivity

theorem eta_factor (b : ℕ) :
    eta b=(1/2:ℝ)^coefficientBits b*(1/2:ℝ)^b/(2:ℝ)^256 := by
  simp [eta,order,pow_add,div_pow]
  ring

theorem epsilon_factor (b : ℕ) :
    epsilon b=(1/2:ℝ)^coefficientBits b*(1/2:ℝ)^b/(2:ℝ)^128 := by
  rw [epsilon,eta_factor]
  norm_num
  ring

theorem half_pow_le_one (n : ℕ) : (1/2:ℝ)^n≤1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem epsilon_le_fixed (b : ℕ) : epsilon b≤1/(2:ℝ)^128 := by
  rw [epsilon_factor]
  gcongr
  exact mul_le_one₀ (half_pow_le_one _) (by positivity) (half_pow_le_one _)

theorem eta_le_fixed (b : ℕ) : eta b≤1/(2:ℝ)^256 := by
  rw [eta_factor]
  gcongr
  exact mul_le_one₀ (half_pow_le_one _) (by positivity) (half_pow_le_one _)

theorem linear_half_pow (b : ℕ) : ((b:ℝ)+1)*(1/2:ℝ)^b≤1 := by
  have hb : (b:ℝ)+1≤(2:ℝ)^b := by
    exact_mod_cast (show b+1≤2^b from Nat.lt_two_pow_self)
  have hh := mul_le_mul_of_nonneg_right hb (show 0≤(1/2:ℝ)^b by positivity)
  simpa [div_pow] using hh

/-- The linear amplitude growth is absorbed by the b extra precision bits. -/
theorem weighted_epsilon (b : ℕ) :
    ((b:ℝ)+1)*epsilon b≤(1/2:ℝ)^coefficientBits b/(2:ℝ)^128 := by
  rw [epsilon_factor]
  have h := mul_le_mul_of_nonneg_left (linear_half_pow b)
    (show 0≤(1/2:ℝ)^coefficientBits b/(2:ℝ)^128 by positivity)
  nlinarith

theorem epsilon_le_eighth (b : ℕ) : epsilon b≤1/8 := by
  have h := epsilon_le_fixed b
  norm_num at h ⊢
  linarith

theorem eta_thirtytwo_le_one (b : ℕ) : 32*eta b≤1 := by
  have h := eta_le_fixed b
  norm_num at h
  linarith

theorem amplitude_epsilon_le_tenth (b : ℕ) : ((b:ℝ)+10)*epsilon b≤1/10 := by
  have h := weighted_epsilon b
  have hp := half_pow_le_one (coefficientBits b)
  have he := epsilon_nonneg b
  norm_num at h
  nlinarith

theorem twelve_epsilon_le_one (b : ℕ) : 12*epsilon b≤1 := by
  have h := epsilon_le_fixed b
  norm_num at h
  linarith

/-- Final raw error is at most one coefficient-grid unit. -/
theorem final_error_budget (b : ℕ) :
    (2:ℝ)^22*((b:ℝ)+1)*epsilon b≤1/(2:ℝ)^coefficientBits b := by
  have h := weighted_epsilon b
  simp only [div_pow,one_pow] at h
  norm_num at h ⊢
  have hp : 0≤((2:ℝ)^coefficientBits b)⁻¹ := by positivity
  nlinarith

theorem epsilon_le_coefficient_unit (b : ℕ) :
    epsilon b≤1/(2:ℝ)^coefficientBits b := by
  have h := final_error_budget b
  have he := epsilon_nonneg b
  have hb : 0≤(b:ℝ) := by positivity
  norm_num at h ⊢
  nlinarith [mul_nonneg hb he]

theorem thirtytwo_eta_le_epsilon (b : ℕ) : 32*eta b≤epsilon b := by
  have h := eta_nonneg b
  unfold epsilon
  norm_num
  nlinarith

theorem four_eta_le_epsilon (b : ℕ) : 4*eta b≤epsilon b := by
  have h := eta_nonneg b
  unfold epsilon
  norm_num
  nlinarith

theorem node_error_le_epsilon (b : ℕ) : (2:ℝ)^125*eta b+64*eta b≤epsilon b := by
  have h := eta_nonneg b
  unfold epsilon
  norm_num
  nlinarith

end PrimeAlgorithm.CertifiedGenerator
