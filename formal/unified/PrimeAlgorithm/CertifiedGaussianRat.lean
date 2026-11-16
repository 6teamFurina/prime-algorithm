import PrimeAlgorithm.CertifiedSeries
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! Computable Gaussian rational arithmetic and Taylor approximations. -/

namespace PrimeAlgorithm.CertifiedGaussianRat

open Finset

abbrev QComplex := QuadraticAlgebra ℚ (-1) 0

instance no_rat_root : Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + 0 * r) := ⟨by
  intro r
  have := sq_nonneg r
  norm_num
  linarith⟩

noncomputable def embed : QComplex →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨Complex.I, by simp⟩

theorem embed_apply (z : QComplex) : embed z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
  change z.re • (1 : ℂ) + z.im • Complex.I = _
  simp [Algebra.smul_def]

@[simp] theorem embed_two : embed (2 : QComplex) = (2 : ℂ) := by
  rw [embed_apply]
  norm_num [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

def expTaylor (m : ℕ) (z : QComplex) : QComplex :=
  ∑ n ∈ range m, z ^ n / (n.factorial : QComplex)

def logTaylor (m : ℕ) (z : QComplex) : QComplex :=
  ∑ n ∈ range m, (-1 : QComplex) ^ (n + 1) * z ^ n / n

def expScaled (m : ℕ) (z : QComplex) : QComplex := (expTaylor m (z / 32)) ^ 32

def logTwo (m : ℕ) : QComplex := -logTaylor m (-1 / 2)

def logScaled (m : ℕ) (z : QComplex) : QComplex := logTwo m + logTaylor m (z / 2 - 1)

def round (p : ℕ) (z : QComplex) : CertifiedCauchy.GaussianIntPair :=
  (CertifiedSeries.roundRat p z.re, CertifiedSeries.roundRat p z.im)

theorem embed_expTaylor (m : ℕ) (z : QComplex) :
    embed (expTaylor m z) = ∑ n ∈ range m, embed z ^ n / (n.factorial : ℂ) := by
  simp [expTaylor]

theorem embed_logTaylor (m : ℕ) (z : QComplex) :
    embed (logTaylor m z) = Complex.logTaylor m (embed z) := by
  simp [logTaylor, Complex.logTaylor]

theorem expTaylor_error (m : ℕ) (z : QComplex) (hz : ‖embed z‖ ≤ 1 / 2) :
    ‖embed (expTaylor m z) - Complex.exp (embed z)‖ ≤ 2 * (1 / 2 : ℝ) ^ m := by
  have hmn : (1 : ℝ) ≤ m + 1 := by
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hdiv : ‖embed z‖ / (m + 1) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have h := Complex.exp_bound' (n := m) (x := embed z) (by simpa using hdiv)
  rw [embed_expTaylor, norm_sub_rev]
  apply h.trans
  have hfac : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
  calc
    _ ≤ ‖embed z‖ ^ m * 2 := by
      apply mul_le_mul_of_nonneg_right (div_le_self (by positivity) hfac) (by norm_num)
    _ ≤ (1 / 2 : ℝ) ^ m * 2 := by gcongr
    _ = _ := mul_comm _ _

theorem logTaylor_error (m : ℕ) (z : QComplex) (hz : ‖embed z‖ ≤ 3 / 4) :
    ‖embed (logTaylor (m + 1) z) - Complex.log (1 + embed z)‖ ≤
      4 * (3 / 4 : ℝ) ^ (m + 1) := by
  rw [embed_logTaylor, norm_sub_rev]
  have h := Complex.norm_log_sub_logTaylor_le m (hz.trans_lt (by norm_num))
  apply h.trans
  have hi : (1 - ‖embed z‖)⁻¹ ≤ (4 : ℝ) := by
    have hd : (1 / 4 : ℝ) ≤ 1 - ‖embed z‖ := by linarith
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hd
    norm_num at this
    exact this
  have hmn : (1 : ℝ) ≤ m + 1 := by
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hinonneg : 0 ≤ (1 - ‖embed z‖)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    _ ≤ ‖embed z‖ ^ (m + 1) * (1 - ‖embed z‖)⁻¹ :=
      div_le_self (by positivity) hmn
    _ ≤ (3 / 4 : ℝ) ^ (m + 1) * 4 := by gcongr
    _ = _ := mul_comm _ _

end PrimeAlgorithm.CertifiedGaussianRat
