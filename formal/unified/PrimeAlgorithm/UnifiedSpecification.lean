import PrimeAlgorithm.PrimePowerInversion
import EthFollowup.Primes.PrimeModEight
import EthFollowup.ModP.EncodeList
import EthFollowup.ModP.SpecSq

/-! A single output function and its binary length bound, shared by the
analytic proof and the counting-machine project. -/
namespace PrimeAlgorithm
open Finset

theorem primeSum_nat_eq_sum_indicator (N : ℕ) :
    primeSum N = ∑ n ∈ range (N+1), if n.Prime then n else 0 := by
  exact_mod_cast primeSum_int_eq_sum_indicator N

theorem primeSum_eq_primeIntervalSum (N : ℕ) :
    primeSum N = EthFollowup.Primes.primeIntervalSum 1 N := by
  rw [primeSum_nat_eq_sum_indicator]
  unfold EthFollowup.Primes.primeIntervalSum
  rw [sum_filter]
  symm
  apply sum_subset
  · intro n hn
    simp only [mem_Icc, mem_range] at hn ⊢
    omega
  · intro n hn hnot
    have : n = 0 := by simp only [mem_Icc, mem_range] at hn hnot; omega
    subst n
    simp

theorem primeSum_le_square (N : ℕ) : primeSum N ≤ N^2 := by
  rw [primeSum_nat_eq_sum_indicator]
  have h : (∑ n ∈ range (N+1), if n.Prime then n else 0) ≤
      ∑ n ∈ range (N+1), if n = 0 then 0 else N := by
    apply sum_le_sum
    intro n hn
    have hle : n ≤ N := by have := mem_range.mp hn; omega
    by_cases hz : n = 0
    · subst n; simp
    · simp only [if_neg hz]
      split_ifs <;> omega
  apply h.trans
  have hf : (range (N+1)).filter (fun n => n ≠ 0) = (range (N+1)).erase 0 := by
    ext n
    simp [and_comm]
  simp only [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, hf]
  simp [pow_two]

theorem primeSum_lt_two_pow {N b : ℕ} (hN : N < 2^b) : primeSum N < 2^(2*b) := by
  apply lt_of_le_of_lt (primeSum_le_square N)
  have h := Nat.pow_lt_pow_left hN (by decide : 2 ≠ 0)
  simpa [← pow_mul, Nat.mul_comm] using h

theorem primeSum_output_length (N : ℕ) :
    (Computability.encodeNat (primeSum N)).length ≤
      2 * (Computability.encodeNat N).length := by
  rw [← EthFollowup.ModP.bits_eq_encodeNat]
  exact EthFollowup.ModP.bits_length_le (primeSum_lt_two_pow
    (EthFollowup.ModP.lt_two_pow_length_encodeNat N))

end PrimeAlgorithm
