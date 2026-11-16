import PrimeAlgorithm.CertifiedGaussianRat

namespace PrimeAlgorithm.CertifiedGaussianRat

open Finset

/-- A fixed initial offset permits direct Taylor evaluation on the whole
bounded argument domain; no repeated-squaring error analysis is needed. -/
theorem expTaylor_large_error (k : ℕ) (z : QComplex) (hz : ‖embed z‖ ≤ 16) :
    ‖embed (expTaylor (31 + k) z) - Complex.exp (embed z)‖ ≤
      (2 : ℝ) ^ 125 * (1 / 2 : ℝ) ^ k := by
  have hk : (0 : ℝ) ≤ k := by positivity
  have hdiv : ‖embed z‖ / ((31 + k : ℕ) + 1) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    push_cast
    linarith
  have h := Complex.exp_bound' (n := 31 + k) (x := embed z) (by simpa using hdiv)
  have hfacN : 32 ^ k ≤ (31 + k).factorial := by
    calc
      _ = 1 * 32 ^ k := by simp
      _ ≤ (31).factorial * 32 ^ k := Nat.mul_le_mul_right _ (Nat.factorial_pos 31)
      _ ≤ _ := Nat.factorial_mul_pow_le_factorial
  have hfac : (32 : ℝ) ^ k ≤ (31 + k).factorial := by exact_mod_cast hfacN
  rw [embed_expTaylor, norm_sub_rev]
  apply h.trans
  calc
    _ ≤ (16 : ℝ) ^ (31 + k) / 32 ^ k * 2 := by gcongr
    _ = (2 * (16 : ℝ) ^ 31) * ((16 : ℝ) / 32) ^ k := by
      rw [pow_add, div_pow]
      ring
    _ = (2 : ℝ) ^ 125 * (1 / 2 : ℝ) ^ k := by norm_num

theorem exp_difference_bound (u v : ℂ) (h : ‖u - v‖ ≤ 1) :
    ‖Complex.exp u - Complex.exp v‖ ≤ 2 * ‖Complex.exp v‖ * ‖u - v‖ := by
  have he : Complex.exp u - Complex.exp v =
      Complex.exp v * (Complex.exp (u - v) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    ring_nf
  rw [he, norm_mul]
  calc
    _ ≤ ‖Complex.exp v‖ * (2 * ‖u - v‖) :=
      mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le h) (norm_nonneg _)
    _ = _ := by ring

theorem logTwo_error (m : ℕ) :
    ‖embed (logTwo (m + 1)) - (Real.log 2 : ℂ)‖ ≤
      4 * (3 / 4 : ℝ) ^ (m + 1) := by
  have h := logTaylor_error m (-1 / 2) (by norm_num [map_div₀, map_neg, map_one])
  have he : Complex.log (1 + embed (-1 / 2 : QComplex)) = -(Real.log 2 : ℂ) := by
    have ht := Complex.log_ofReal_mul (r := 2) (by norm_num) (x := (1 / 2 : ℂ)) (by norm_num)
    norm_num at ht
    norm_num [map_div₀, map_neg, map_one]
    simpa using eq_neg_of_add_eq_zero_right ht.symm
  rw [he] at h
  rw [logTwo, map_neg]
  rw [show -embed (logTaylor (m + 1) (-1 / 2)) - (Real.log 2 : ℂ) =
    -(embed (logTaylor (m + 1) (-1 / 2)) - -(Real.log 2 : ℂ)) by ring, norm_neg]
  exact h

theorem logScaled_error (m : ℕ) (z : QComplex)
    (hz : ‖embed z / 2 - 1‖ ≤ 3 / 4) (hz0 : embed z ≠ 0) :
    ‖embed (logScaled (m + 1) z) - Complex.log (embed z)‖ ≤
      8 * (3 / 4 : ℝ) ^ (m + 1) := by
  have htwo := logTwo_error m
  have hlog := logTaylor_error m (z / 2 - 1) (by simpa using hz)
  have hid : Complex.log (embed z) = (Real.log 2 : ℂ) + Complex.log (embed z / 2) := by
    have h := Complex.log_ofReal_mul (r := 2) (by norm_num)
      (x := embed z / 2) (div_ne_zero hz0 (by norm_num))
    convert h using 1 <;> push_cast <;> congr 1 <;> ring
  have ht := norm_add_le
    (embed (logTwo (m + 1)) - (Real.log 2 : ℂ))
    (embed (logTaylor (m + 1) (z / 2 - 1)) - Complex.log (embed z / 2))
  have he : embed (logScaled (m + 1) z) - Complex.log (embed z) =
      (embed (logTwo (m + 1)) - (Real.log 2 : ℂ)) +
      (embed (logTaylor (m + 1) (z / 2 - 1)) - Complex.log (embed z / 2)) := by
    rw [logScaled, map_add, hid]
    ring
  rw [he]
  have hlog' : ‖embed (logTaylor (m + 1) (z / 2 - 1)) - Complex.log (embed z / 2)‖ ≤
      4 * (3 / 4 : ℝ) ^ (m + 1) := by simpa using hlog
  linarith

end PrimeAlgorithm.CertifiedGaussianRat
