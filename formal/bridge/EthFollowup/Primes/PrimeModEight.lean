/-
Exact mod-eight reconstruction from the first two weighted pointwise moments.
This file uses the upstream witness theorem, but no machine-time assumptions.
-/
import EthFollowup.Primes.ChainParity

namespace EthFollowup.Primes

open Finset

theorem chainCount_of_squarefree (L : ℕ) {n : ℕ} (hn : Squarefree n) :
    chainCount L n = 1 := by
  induction L generalizing n with
  | zero => rfl
  | succ L ih =>
    have hs : n.divisors.filter (fun d => d * d ∣ n) = {1} := by
      ext d
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨_, hd⟩
        exact Nat.isUnit_iff.mp (hn d hd)
      · rintro rfl
        simp [Nat.mem_divisors, hn.ne_zero]
    rw [chainCount, hs, sum_singleton]
    exact ih (by simp)

def primeWitness (L n : ℕ) : ℕ := tauLt n * chainCount L n

theorem primeWitness_prime (L : ℕ) {p : ℕ} (hp : p.Prime) :
    primeWitness L p = 1 := by
  simp [primeWitness, tauLt_prime hp, chainCount_of_squarefree L hp.squarefree]

theorem primeWitness_nonprime_even {L n : ℕ} (hn : n < 2 ^ 2 ^ L)
    (hp : ¬ n.Prime) : primeWitness L n % 2 = 0 := by
  have h := zmod_two_to_mod (term_zmod hn)
  simpa [primeWitness, hp] using h

theorem quadratic_mod_eight_of_even (n : ℕ) (hn : n % 2 = 0) :
    2 * (n : ZMod 8) - (n : ZMod 8) ^ 2 = 0 := by
  have hm : (n % 8) % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 8)]
    exact hn
  have hr : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have heq : (n : ZMod 8) = ((n % 8 : ℕ) : ZMod 8) := by simp
  rw [heq]
  obtain h | h | h | h : n % 8 = 0 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 := by omega
  all_goals rw [h]; decide

theorem primeWitness_quadratic {L n : ℕ} (hn : n < 2 ^ 2 ^ L) :
    2 * (primeWitness L n : ZMod 8) - (primeWitness L n : ZMod 8) ^ 2 =
      if n.Prime then 1 else 0 := by
  by_cases hp : n.Prime
  · rw [primeWitness_prime L hp, if_pos hp]
    norm_num
  · rw [if_neg hp]
    exact quadratic_mod_eight_of_even _ (primeWitness_nonprime_even hn hp)

def weightedMoment (r L A B : ℕ) : ℕ :=
  ∑ n ∈ Icc A B, n * primeWitness L n ^ r

def primeIntervalSum (A B : ℕ) : ℕ :=
  ∑ n ∈ (Icc A B).filter Nat.Prime, n

theorem weightedMoment_mod_eight {L A B : ℕ} (hB : B < 2 ^ 2 ^ L) :
    2 * (weightedMoment 1 L A B : ZMod 8) - (weightedMoment 2 L A B : ZMod 8) =
      (primeIntervalSum A B : ZMod 8) := by
  unfold weightedMoment primeIntervalSum
  push_cast
  rw [mul_sum, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro n hn
  have h := primeWitness_quadratic (L := L) (n := n) (by
    have := (mem_Icc.mp hn).2
    omega)
  have heq : 2 * ((n : ZMod 8) * primeWitness L n ^ 1) -
      (n : ZMod 8) * primeWitness L n ^ 2 =
      (n : ZMod 8) * (2 * primeWitness L n - primeWitness L n ^ 2) := by ring
  rw [heq, h]
  split_ifs <;> simp

/-- Natural-number interface, with a safe subtraction of residues. -/
theorem weightedMoment_residue_eight {L A B : ℕ} (hB : B < 2 ^ 2 ^ L) :
    (2 * (weightedMoment 1 L A B % 8) + 8 - weightedMoment 2 L A B % 8) % 8 =
      primeIntervalSum A B % 8 := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ 8).mp
  have hle : weightedMoment 2 L A B % 8 ≤ 2 * (weightedMoment 1 L A B % 8) + 8 := by omega
  rw [Nat.cast_sub hle]
  have h8 : (8 : ZMod 8) = 0 := by decide
  simpa [h8] using weightedMoment_mod_eight (A := A) hB

end EthFollowup.Primes
