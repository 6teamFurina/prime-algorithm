import PrimeAlgorithm.CertifiedRawTaylor
import PrimeAlgorithm.CertifiedSeries

set_option maxHeartbeats 1500000

namespace PrimeAlgorithm.CertifiedRawPi

open Finset Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib CertifiedRawGaussian
  CertifiedRawTaylor CertifiedGaussianRat CertifiedSeries

def atanNumerator (m q : ℕ) : ℤ :=
  ∑ k ∈ range m, (-1 : ℤ) ^ k * (q : ℤ) ^ (2 * m + 1 - (2 * k + 1)) *
    ((2 * m + 1).factorial / (2 * k + 1) : ℕ)

def atan (m q : ℕ) : Raw :=
  (atanNumerator m q, 0, (2 * m + 1).factorial * q ^ (2 * m + 1))

def pi (m : ℕ) : Raw := mul (ofInt 4) (add (atan m 2) (atan m 3))

theorem atan_valid (m : ℕ) {q : ℕ} (hq : 0 < q) : Valid (atan m q) :=
  Nat.mul_pos (Nat.factorial_pos _) (pow_pos hq _)

theorem pi_valid (m : ℕ) : Valid (pi m) :=
  valid_mul (valid_ofInt 4) (valid_add (atan_valid m (by decide)) (atan_valid m (by decide)))

theorem atan_correct (m : ℕ) {q : ℕ} (hq : 0 < q) :
    embed (interpret (atan m q)) = (atanRat m (1 / q) : ℂ) := by
  rw [embed_interpret]
  simp only [atan, atanNumerator, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, Int.cast_zero, zero_mul, add_zero,
    Nat.cast_mul, Nat.cast_pow, atanRat, Rat.cast_sum, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast, Rat.cast_add]
  rw [sum_div]
  apply sum_congr rfl
  intro k hk
  have hkm : 2 * k + 1 ≤ 2 * m + 1 := by have := mem_range.mp hk; omega
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hF : ((2 * m + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hK : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * k + 1 ≠ 0)
  rw [Nat.cast_div (Nat.dvd_factorial (by omega) hkm) hK]
  have hpow : (q : ℂ) ^ (2 * m + 1) =
      (q : ℂ) ^ (2 * k + 1) * (q : ℂ) ^ (2 * m + 1 - (2 * k + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le hkm]
  rw [hpow, div_pow]
  push_cast
  field_simp
  simp

theorem pi_correct (m : ℕ) : embed (interpret (pi m)) = (piRat m : ℂ) := by
  rw [pi, interpret_mul (valid_ofInt 4)
    (valid_add (atan_valid m (by decide)) (atan_valid m (by decide))),
    interpret_add (atan_valid m (by decide)) (atan_valid m (by decide))]
  simp only [map_mul, map_add, interpret_ofInt, map_intCast,
    piRat, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add]
  rw [atan_correct m (show 0 < 2 by decide), atan_correct m (show 0 < 3 by decide)]
  norm_num

theorem atanNumerator_polyT {α : Type} [Enc α] {m q : α → ℕ}
    (hm : Unary m) (hq : PolyT q) : PolyT (fun x => atanNumerator (m x) (q x)) := by
  have hM : Unary (fun p : α × ℕ => m p.1) := hm.comp PolyT.id'.fst
  have hK : Unary (fun p : α × ℕ => min p.2 (m p.1)) :=
    unary_min_right PolyT.id'.snd hM
  have hL : Unary (fun p : α × ℕ => 2 * m p.1 + 1) := by fun_prop
  have hJ : Unary (fun p : α × ℕ => 2 * min p.2 (m p.1) + 1) := by fun_prop
  have hQ : PolyT (fun p : α × ℕ => (q p.1 : ℤ)) :=
    PolyT.natCast (hq.comp PolyT.id'.fst)
  have hsgn := powZ_polyT (PolyT.const (-1)) hK
  have hp := powZ_polyT hQ (unary_sub hL hJ.poly)
  have hf := factorial_polyT hL
  have hd : PolyT (fun p : α × ℕ =>
      (((2 * m p.1 + 1).factorial / (2 * min p.2 (m p.1) + 1) : ℕ) : ℤ)) := by
    have hJpoly := hJ.poly
    fun_prop
  apply sum_range_polyT (f := fun x k => (-1 : ℤ) ^ k *
    (q x : ℤ) ^ (2 * m x + 1 - (2 * k + 1)) *
      (((2 * m x + 1).factorial / (2 * k + 1) : ℕ) : ℤ)) hm
  exact PolyT.mulZ (PolyT.mulZ hsgn hp) hd

theorem atan_polyT {α : Type} [Enc α] {m q : α → ℕ}
    (hm : Unary m) (hq : PolyT q) : PolyT (fun x => atan (m x) (q x)) := by
  have hL : Unary (fun x => 2 * m x + 1) := by fun_prop
  exact PolyT.prodMk (atanNumerator_polyT hm hq) (PolyT.prodMk (PolyT.const 0)
    (PolyT.mul (factorial_polyT hL) (PolyT.pow_unary hq hL)))

theorem pi_polyT {α : Type} [Enc α] {m : α → ℕ} (hm : Unary m) :
    PolyT (fun x => pi (m x)) := by
  have hA := atan_polyT hm (PolyT.const 2)
  have hB := atan_polyT hm (PolyT.const 3)
  exact mul_apply_polyT (PolyT.const (ofInt 4)) (add_apply_polyT hA hB)

end PrimeAlgorithm.CertifiedRawPi
