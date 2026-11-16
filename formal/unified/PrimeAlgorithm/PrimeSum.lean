module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime

public section

namespace PrimeAlgorithm

/-- The exact sum of all primes less than or equal to `n`.
This direct definition specifies the mathematical function, not a fast algorithm. -/
def primeSum (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter Nat.Prime).sum id

@[simp]
theorem primeSum_zero : primeSum 0 = 0 := by
  norm_num [primeSum]

theorem primeSum_succ (n : ℕ) :
    primeSum (n + 1) = primeSum n + (if Nat.Prime (n + 1) then n + 1 else 0) := by
  simp [primeSum, Finset.sum_filter, Finset.sum_range_succ]

theorem primeSum_thirty : primeSum 30 = 129 := by
  norm_num [primeSum, Finset.sum_filter, Finset.sum_range_succ]

end PrimeAlgorithm
