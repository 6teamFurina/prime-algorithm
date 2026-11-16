import PrimeAlgorithm.PrimeCountFormula
import PrimeAlgorithm.IntegerPrimeSum

/-! Exact integer reconstruction for prime counting, using the same certified
coefficient tables and four numerator factors as prime summation. -/

namespace PrimeAlgorithm.PrimeCountInteger
open Finset CertifiedCauchy CertifiedNumerator CertifiedPrimeSum DoubleRamanujan
  IntegerPrimeSum PrimeCountFormula

def integerPrimeCount (b : ℕ) (D : PrimeData) (N : ℕ) : GaussianIntPair :=
  -(∑ n ∈ Icc 2 N, ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
    ∑ y ∈ unitsBelow d, productNumerator b D n d x y)

def integerResult (b : ℕ) (D : PrimeData) (N : ℕ) : ℤ :=
  (2*(integerPrimeCount b D N).1+(commonScale b:ℤ)^4)/(2*(commonScale b:ℤ)^4)

/-- The entire approximate prime count has one explicitly known denominator. -/
theorem approximatePrimeCount_spec (b : ℕ) (D : PrimeData) (N : ℕ) :
    approximatePrimeCount b D N = embed (integerPrimeCount b D N)/(commonScale b:ℂ)^4 := by
  unfold approximatePrimeCount phaseCount integerPrimeCount
  rw [embed_neg,neg_div]
  congr 1
  simp_rw [embed_sum,sum_div]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro y hy
  have hnp : 0<n := by have := (mem_Icc.mp hn).1; omega
  rw [logNumerator_spec,invLogNumerator_spec,phaseNumerator_spec b D n x hnp,
    phaseNumerator_spec b D d y (Nat.pos_of_mem_divisors hd)]
  simp only [productNumerator,embed_multiply]
  ring

theorem integerResult_eq_round (b : ℕ) (D : PrimeData) (N : ℕ) :
    integerResult b D N = ⌊(approximatePrimeCount b D N).re+1/2⌋ := by
  rw [approximatePrimeCount_spec]
  have he : (embed (integerPrimeCount b D N)/(commonScale b:ℂ)^4).re =
      ((integerPrimeCount b D N).1:ℝ)/(commonScale b^4:ℕ) := by
    rw [show (commonScale b:ℂ)^4=(((commonScale b^4:ℕ):ℝ):ℂ) by
      simp only [Nat.cast_pow,Complex.ofReal_pow,Complex.ofReal_natCast]]
    simp only [Complex.div_ofReal_re,embed,Complex.add_re,Complex.intCast_re,
      Complex.mul_re,Complex.intCast_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_zero,add_zero]
  rw [he,rational_round _ _ (pow_pos (commonScale_pos b) 4)]
  simp only [integerResult,Nat.cast_pow]

/-- Pure integer division recovers the exact prime count from any certified table. -/
theorem integerResult_eq_primeCounting {N b : ℕ} {D : PrimeData}
    (hN : N ≤ 2^b) (hD : Certified b D) : integerResult b D N=(Nat.primeCounting N:ℤ) := by
  rw [integerResult_eq_round]
  exact PrimeCountFormula.primeCounting_round hN hD

theorem integerResult_all_inputs (N : ℕ) (D : PrimeData)
    (hD : Certified (Nat.log 2 N+1) D) :
    integerResult (Nat.log 2 N+1) D N=(Nat.primeCounting N:ℤ) :=
  integerResult_eq_primeCounting (Nat.lt_pow_succ_log_self (by decide) N).le hD

end PrimeAlgorithm.PrimeCountInteger
