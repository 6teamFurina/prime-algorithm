import PrimeAlgorithm.CertifiedCauchy
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Rational Taylor algorithms with explicit geometric error bounds.
All definitions in the first section compute using rational arithmetic only. -/

namespace PrimeAlgorithm.CertifiedSeries

open Finset

def atanRat (m : ℕ) (x : ℚ) : ℚ :=
  ∑ n ∈ range m, (-1 : ℚ) ^ n * x ^ (2 * n + 1) / (2 * n + 1)

def piRat (m : ℕ) : ℚ := 4 * (atanRat m (1 / 2) + atanRat m (1 / 3))

def roundRat (p : ℕ) (x : ℚ) : ℤ := ⌊(2 : ℚ) ^ p * x⌋

theorem atanRat_cast (m : ℕ) (x : ℚ) :
    (atanRat m x : ℝ) =
      ∑ n ∈ range m, (-1 : ℝ) ^ n * (x : ℝ) ^ (2 * n + 1) / (2 * n + 1) := by
  simp [atanRat]

theorem atan_tail {x : ℝ} (hx : |x| ≤ 1 / 2) (m : ℕ) :
    |Real.arctan x - ∑ n ∈ range m,
      (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1)| ≤
      (1 / 4 : ℝ) ^ m / (1 - 1 / 4) := by
  let a : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1)
  have hsum : HasSum (fun n => (a n : ℂ)) (Real.arctan x : ℂ) := by
    apply Complex.hasSum_ofReal.mpr
    simpa [a] using Real.hasSum_arctan (by simpa only [Real.norm_eq_abs] using
      (hx.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)))
  have hc : ∀ n, ‖(a n : ℂ)‖ ≤ 1 * (1 / 4 : ℝ) ^ n := by
    intro n
    have hden : (1 : ℝ) ≤ 2 * n + 1 := by
      have : (0 : ℝ) ≤ n := by positivity
      linarith
    have hn : ‖(a n : ℂ)‖ = |x| ^ (2 * n + 1) / (2 * n + 1) := by
      simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
        abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * n + 1)]
    rw [hn, one_mul]
    calc
      _ ≤ |x| ^ (2 * n + 1) := div_le_self (by positivity) hden
      _ = (|x| ^ 2) ^ n * |x| := by rw [pow_add, pow_one, pow_mul]
      _ ≤ (1 / 4 : ℝ) ^ n * 1 := by
        have hs : |x| ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith [abs_nonneg x]
        gcongr
        exact hx.trans (by norm_num)
      _ = _ := mul_one _
  have h := (Cauchy.series_tail_bound (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1) hc m).2
  rw [hsum.tsum_eq, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, one_mul] at h
  exact h

theorem piRat_error (m : ℕ) :
    |(piRat m : ℝ) - Real.pi| ≤ 16 * (1 / 4 : ℝ) ^ m := by
  have h₂ := atan_tail (x := 1 / 2) (by norm_num) m
  have h₃ := atan_tail (x := 1 / 3) (by norm_num) m
  have hp := Real.arctan_inv_2_add_arctan_inv_3
  have hsum := abs_add_le
    ((atanRat m (1 / 2) : ℝ) - Real.arctan (1 / 2))
    ((atanRat m (1 / 3) : ℝ) - Real.arctan (1 / 3))
  rw [atanRat_cast, atanRat_cast] at hsum
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hsum
  rw [abs_sub_comm _ (Real.arctan (1 / 2)), abs_sub_comm _ (Real.arctan (1 / 3))] at hsum
  have hid : (piRat m : ℝ) - Real.pi =
      4 * (((atanRat m (1 / 2) : ℝ) - Real.arctan (1 / 2)) +
        ((atanRat m (1 / 3) : ℝ) - Real.arctan (1 / 3))) := by
    simp only [piRat, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat]
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
      show (1 / 3 : ℝ) = 3⁻¹ by norm_num]
    linarith
  rw [hid, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [atanRat_cast, atanRat_cast]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  norm_num at h₂ h₃
  linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) m]

end PrimeAlgorithm.CertifiedSeries
