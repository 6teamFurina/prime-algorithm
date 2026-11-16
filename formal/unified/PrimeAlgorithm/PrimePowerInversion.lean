module

public import PrimeAlgorithm.PrimeSum
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Tactic

public section

namespace PrimeAlgorithm

open Finset
open scoped ArithmeticFunction.Moebius

/-- The divisor Möbius cancellation, including exponent zero. -/
theorem exponent_moebius_sum (e : ℕ) :
    (∑ a ∈ e.divisors, μ a) = if e = 1 then (1 : ℤ) else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- A positive prime-power root of p^e has the same prime and a dividing exponent.
This explicitly proves the uniqueness needed in the later finite reindexing. -/
theorem primePower_root_unique {p e m a : ℕ} (hp : p.Prime) (he : 0 < e)
    (hm : IsPrimePow m) (ha : 0 < a) (hpow : m ^ a = p ^ e) :
    a ∣ e ∧ m = p ^ (e / a) := by
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff m).1 hm
  rw [← pow_mul] at hpow
  obtain ⟨hqp, hke⟩ := hq.pow_inj' hp (Nat.mul_pos hk ha).ne' he.ne' hpow
  subst q
  refine ⟨⟨k, hke.symm.trans (Nat.mul_comm k a)⟩, ?_⟩
  congr 1
  rw [← hke, Nat.mul_div_cancel _ ha]

/-- Every exact root with base at least 2 has a logarithmically bounded exponent. -/
theorem exact_root_exponent_le_log {m a N : ℕ} (hm : 2 ≤ m) (hpow : m ^ a ≤ N) :
    a ≤ Nat.log 2 N :=
  Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_left hm a).trans hpow)

/-- Exact roots, with all bounds explicit and no floating-point integer roots. -/
def primePowerRoots (N n : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (Nat.log 2 N)).product (Icc 2 N)).filter
    (fun am => IsPrimePow am.2 ∧ am.2 ^ am.1 = n)

theorem mem_primePowerRoots {N n a m : ℕ} :
    (a, m) ∈ primePowerRoots N n ↔
      1 ≤ a ∧ a ≤ Nat.log 2 N ∧ 2 ≤ m ∧ m ≤ N ∧ IsPrimePow m ∧ m ^ a = n := by
  simp [primePowerRoots, and_assoc]

theorem primePowerRoots_prime_pow {N p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hN : p ^ e ≤ N) :
    (∑ am ∈ primePowerRoots N (p ^ e), μ am.1) = ∑ a ∈ e.divisors, μ a := by
  symm
  apply sum_bij (fun a _ => (a, p ^ (e / a)))
  · intro a ha
    have had : a ∣ e := (Nat.mem_divisors.1 ha).1
    have hap : 0 < a := Nat.pos_of_mem_divisors ha
    have hae : a ≤ e := Nat.le_of_dvd he had
    have hep : 0 < e / a := Nat.div_pos hae hap
    have hroot : (p ^ (e / a)) ^ a = p ^ e := by
      rw [← pow_mul, Nat.div_mul_cancel had]
    have hpp : IsPrimePow (p ^ (e / a)) := hp.isPrimePow.pow hep.ne'
    refine mem_primePowerRoots.2 ⟨hap, ?_, hpp.two_le, ?_, hpp, hroot⟩
    · exact exact_root_exponent_le_log hpp.two_le (hroot ▸ hN)
    · exact (Nat.le_pow hap).trans (hroot ▸ hN)
  · intro a ha a' ha' h
    exact Prod.mk.inj h |>.1
  · rintro ⟨a, m⟩ ham
    obtain ⟨ha, _, _, _, hm, hpow⟩ := mem_primePowerRoots.1 ham
    obtain ⟨had, hroot⟩ := primePower_root_unique hp he hm ha hpow
    exact ⟨a, Nat.mem_divisors.2 ⟨had, he.ne'⟩, by simp [hroot]⟩
  · intro a ha
    rfl

/-- Exponent Möbius inversion turns prime-power roots into the prime indicator. -/
theorem primePowerRoots_moebius {N n : ℕ} (hn : n ≤ N) :
    (∑ am ∈ primePowerRoots N n, μ am.1) = if n.Prime then (1 : ℤ) else 0 := by
  by_cases hpp : IsPrimePow n
  · obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    rw [primePowerRoots_prime_pow hp he hn, exponent_moebius_sum]
    have hprime : (p ^ e).Prime ↔ e = 1 := by
      constructor
      · intro h
        exact (h.pow_eq_iff.mp rfl).2
      · rintro rfl
        simpa using hp
    simp only [hprime]
  · have hempty : primePowerRoots N n = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      rintro ⟨a, m⟩ ham
      obtain ⟨ha, _, _, _, hm, hpow⟩ := mem_primePowerRoots.1 ham
      exact hpp (hpow ▸ hm.pow (by omega))
    have hnp : ¬n.Prime := fun hp => hpp hp.isPrimePow
    simp [hempty, hnp]

/-- All prime-power bases and positive exponents whose powers are at most N. -/
@[expose] def primePowerPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (Nat.log 2 N)).product (Icc 2 N)).filter
    (fun am => IsPrimePow am.2 ∧ am.2 ^ am.1 ≤ N)

theorem primePowerPairs_def (N : ℕ) : primePowerPairs N =
    ((Icc 1 (Nat.log 2 N)).product (Icc 2 N)).filter
      (fun am => IsPrimePow am.2 ∧ am.2 ^ am.1 ≤ N) := rfl

theorem primePowerRoots_eq_fiber {N n : ℕ} (hn : n ≤ N) :
    primePowerRoots N n = (primePowerPairs N).filter (fun am => am.2 ^ am.1 = n) := by
  ext am
  simp only [primePowerRoots, primePowerPairs, mem_filter]
  constructor
  · rintro ⟨ham, hm, hpow⟩
    exact ⟨⟨ham, hm, hpow ▸ hn⟩, hpow⟩
  · rintro ⟨⟨ham, hm, _⟩, hpow⟩
    exact ⟨ham, hm, hpow⟩

theorem primePowerRoots_weighted {N n : ℕ} (hn : n ≤ N) (w : ℕ → ℤ) :
    (∑ am ∈ primePowerRoots N n, μ am.1 * w (am.2 ^ am.1)) =
      if n.Prime then w n else 0 := by
  calc
    (∑ am ∈ primePowerRoots N n, μ am.1 * w (am.2 ^ am.1)) =
        ∑ am ∈ primePowerRoots N n, μ am.1 * w n := by
      apply sum_congr rfl
      intro am ham
      rw [(mem_primePowerRoots.1 ham).2.2.2.2.2]
    _ = (∑ am ∈ primePowerRoots N n, μ am.1) * w n := (sum_mul ..).symm
    _ = if n.Prime then w n else 0 := by
      rw [primePowerRoots_moebius hn]
      split_ifs <;> simp

/-- Finite exponent Möbius inversion with an arbitrary integer weight.
The equality is a reindexing of explicit finite sets, not an appeal to
convergence of prime-zeta or Dirichlet series. -/
theorem weightedPrimeSum_moebius_pairs (N : ℕ) (w : ℕ → ℤ) :
    (∑ am ∈ primePowerPairs N, μ am.1 * w (am.2 ^ am.1)) =
      ∑ n ∈ range (N + 1), if n.Prime then w n else 0 := by
  have hmap : ∀ am ∈ primePowerPairs N, am.2 ^ am.1 ∈ range (N + 1) := by
    intro am ham
    simp only [primePowerPairs, mem_filter] at ham
    exact mem_range.2 (by omega)
  calc
    (∑ am ∈ primePowerPairs N, μ am.1 * w (am.2 ^ am.1)) =
        ∑ n ∈ range (N + 1), ∑ am ∈ (primePowerPairs N).filter
          (fun am => am.2 ^ am.1 = n), μ am.1 * w (am.2 ^ am.1) :=
      (sum_fiberwise_of_maps_to hmap (fun am => μ am.1 * w (am.2 ^ am.1))).symm
    _ = ∑ n ∈ range (N + 1), if n.Prime then w n else 0 := by
      apply sum_congr rfl
      intro n hn
      have hnN : n ≤ N := by simpa using mem_range.1 hn
      rw [← primePowerRoots_eq_fiber hnN]
      exact primePowerRoots_weighted hnN w

/-- A weighted sum over prime powers whose a-th powers are at most N.
For w(n)=n this is precisely A_a(floor(N^(1/a))), stated without a floor-root API. -/
@[expose] def weightedPrimePowerSum (N a : ℕ) (w : ℕ → ℤ) : ℤ :=
  ∑ m ∈ (Icc 2 N).filter (fun m => IsPrimePow m ∧ m ^ a ≤ N), w (m ^ a)

theorem weightedPrimePowerSum_eq (N a : ℕ) (w : ℕ → ℤ) :
    weightedPrimePowerSum N a w =
      ∑ m ∈ (Icc 2 N).filter (fun m => IsPrimePow m ∧ m ^ a ≤ N), w (m ^ a) := rfl

theorem primePowerPairs_sum (N : ℕ) (w : ℕ → ℤ) :
    (∑ am ∈ primePowerPairs N, μ am.1 * w (am.2 ^ am.1)) =
      ∑ a ∈ Icc 1 (Nat.log 2 N), μ a * weightedPrimePowerSum N a w := by
  simp only [primePowerPairs, weightedPrimePowerSum, sum_filter, mul_sum]
  rw [product_eq_sprod, sum_product]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro m hm
  split_ifs <;> simp

/-- The complete finite weighted inversion, with the exponent cutoff floor(log₂ N). -/
theorem weightedPrimeSum_moebius (N : ℕ) (w : ℕ → ℤ) :
    (∑ n ∈ range (N + 1), if n.Prime then w n else 0) =
      ∑ a ∈ Icc 1 (Nat.log 2 N), μ a * weightedPrimePowerSum N a w := by
  rw [← weightedPrimeSum_moebius_pairs, primePowerPairs_sum]

/-- Connect the public primeSum API without unfolding its sealed definition. -/
theorem primeSum_int_eq_sum_indicator (N : ℕ) :
    (primeSum N : ℤ) = ∑ n ∈ range (N + 1), if n.Prime then (n : ℤ) else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [primeSum_succ, Nat.cast_add, ih]
    conv_rhs => rw [sum_range_succ]
    congr 1
    split_ifs <;> simp

/-- Exact prime summation recovered from weighted prime-power sums.
This is an integer equality; no modulus or asymptotic argument is involved. -/
theorem primeSum_moebius_primePowerSum (N : ℕ) :
    (primeSum N : ℤ) =
      ∑ a ∈ Icc 1 (Nat.log 2 N), μ a *
        ∑ m ∈ (Icc 2 N).filter (fun m => IsPrimePow m ∧ m ^ a ≤ N), (m : ℤ) ^ a := by
  have h := weightedPrimeSum_moebius N (fun n => (n : ℤ))
  rw [primeSum_int_eq_sum_indicator]
  simpa [weightedPrimePowerSum, sum_filter] using h

end PrimeAlgorithm
