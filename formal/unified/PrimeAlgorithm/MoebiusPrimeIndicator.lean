module

public import PrimeAlgorithm.PrimePowerInversion
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic

public section

namespace PrimeAlgorithm

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

/-- A second Möbius factor removes all proper prime powers pointwise.
This identity is valid also at 0 and 1, with the field convention for division. -/
theorem moebius_vonMangoldt_primeIndicator (n : ℕ) :
    -(μ n : ℝ) * Λ n / Real.log n = if n.Prime then 1 else 0 := by
  by_cases hp : n.Prime
  · have hl : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp [hp, ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.vonMangoldt_apply_prime hp, hl]
  · by_cases hpp : IsPrimePow n
    · simp [hp, ArithmeticFunction.moebius_apply_isPrimePow_not_prime hpp hp]
    · simp [hp, ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]

/-- Constant-arity prime summation: no exponent-root correction is required. -/
theorem primeSum_moebius_vonMangoldt (N : ℕ) :
    (primeSum N : ℝ) =
      ∑ n ∈ range (N + 1),
        -(n : ℝ) * (μ n : ℝ) * Λ n / Real.log n := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (primeSum_int_eq_sum_indicator N)
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_ite, Int.cast_zero] at h
  rw [h]
  apply sum_congr rfl
  intro n hn
  calc
    (if n.Prime then (n : ℝ) else 0) =
        (n : ℝ) * (if n.Prime then 1 else 0) := by split_ifs <;> simp
    _ = (n : ℝ) * (-(μ n : ℝ) * Λ n / Real.log n) := by
      rw [moebius_vonMangoldt_primeIndicator]
    _ = _ := by ring

end PrimeAlgorithm
