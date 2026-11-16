import PrimeAlgorithm.CertifiedNumerator
import PrimeAlgorithm.CertifiedPrimeSum

set_option maxHeartbeats 2000000

/-! A purely integer numerator and integer-division endpoint for the certified
prime-sum formula. No real-number operation occurs in these definitions. -/

namespace PrimeAlgorithm.IntegerPrimeSum

open Finset PrimeAlgorithm.CertifiedCauchy PrimeAlgorithm.CertifiedNumerator
  PrimeAlgorithm.CertifiedPrimeSum PrimeAlgorithm.DoubleRamanujan

def commonScale (b : ℕ) : ℕ := scale (coefficientBits b) (reciprocalBits b) (nodeCount b)

def logNumerator (b : ℕ) (D : PrimeData) (n : ℕ) : GaussianIntPair :=
  if n<2 then (0,0) else
    numerator (coefficientBits b) (reciprocalBits b) (nodeCount b)
      (logData D (Nat.log 2 n)) n (2^Nat.log 2 n)

def invLogNumerator (b : ℕ) (D : PrimeData) (n : ℕ) : GaussianIntPair :=
  numerator (coefficientBits b) (reciprocalBits b) (nodeCount b)
    (invLogData D (Nat.log 2 n)) n (2^Nat.log 2 n)

def phaseNumerator (b : ℕ) (D : PrimeData) (d x : ℕ) : GaussianIntPair :=
  numerator (coefficientBits b) (reciprocalBits b) (nodeCount b) (phaseData D) (d+x) d

def productNumerator (b : ℕ) (D : PrimeData) (n d x y : ℕ) : GaussianIntPair :=
  multiply (multiply (multiply (logNumerator b D (n/d)) (invLogNumerator b D n))
    (phaseNumerator b D n x)) (phaseNumerator b D d y)

def integerPrimeSum (b : ℕ) (D : PrimeData) (N : ℕ) : GaussianIntPair :=
  -(∑ n ∈ Icc 2 N, ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
    ∑ y ∈ unitsBelow d, n • productNumerator b D n d x y)

def integerResult (b : ℕ) (D : PrimeData) (N : ℕ) : ℤ :=
  (2*(integerPrimeSum b D N).1+(commonScale b:ℤ)^4)/(2*(commonScale b:ℤ)^4)

theorem commonScale_pos (b : ℕ) : 0<commonScale b := by
  unfold commonScale scale
  have hm : 0<nodeCount b := Cauchy.primeNodes_pos _
  positivity

@[simp] theorem embed_zero : embed (0:GaussianIntPair)=0 := by simp [embed]
@[simp] theorem embed_neg (z : GaussianIntPair) : embed (-z) = -embed z := by
  simp [embed]
  ring

theorem embed_sum {α : Type} (s : Finset α) (f : α → GaussianIntPair) :
    embed (∑i∈s,f i)=∑i∈s,embed (f i) := by
  simp [embed,Prod.fst_sum,Prod.snd_sum,Int.cast_sum,sum_mul,sum_add_distrib]

theorem embed_nsmul (n : ℕ) (z : GaussianIntPair) : embed (n • z)=(n:ℂ)*embed z := by
  rcases z with ⟨a,b⟩
  simp [embed,nsmul_eq_mul]
  ring

theorem logNumerator_spec (b : ℕ) (D : PrimeData) (n : ℕ) :
    approximateLog b D n = embed (logNumerator b D n)/(commonScale b:ℂ) := by
  by_cases hn : n<2
  · rw [approximateLog,if_pos hn,logNumerator,if_pos hn]
    change 0=embed (0:GaussianIntPair)/(commonScale b:ℂ)
    rw [embed_zero,zero_div]
  · simp only [approximateLog,logNumerator,if_neg hn,primeEvaluate,
      CauchyPrimeSum.mantissa,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    simpa only [commonScale,Nat.cast_pow,Nat.cast_ofNat] using
      numerator_spec (coefficientBits b) (reciprocalBits b) (nodeCount b)
        (logData D (Nat.log 2 n)) n (2^Nat.log 2 n) (by positivity)

theorem invLogNumerator_spec (b : ℕ) (D : PrimeData) (n : ℕ) :
    approximateInvLog b D n = embed (invLogNumerator b D n)/(commonScale b:ℂ) := by
  simp only [approximateInvLog,invLogNumerator,primeEvaluate,
    CauchyPrimeSum.mantissa,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  simpa only [commonScale,Nat.cast_pow,Nat.cast_ofNat] using
    numerator_spec (coefficientBits b) (reciprocalBits b) (nodeCount b)
      (invLogData D (Nat.log 2 n)) n (2^Nat.log 2 n) (by positivity)

theorem phaseNumerator_spec (b : ℕ) (D : PrimeData) (d x : ℕ) (hd : 0<d) :
    approximatePhase b D d x = embed (phaseNumerator b D d x)/(commonScale b:ℂ) := by
  have hd' : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  have he : (1:ℂ)+(x:ℂ)/d=((d+x:ℕ):ℂ)/d := by push_cast; field_simp
  simp only [approximatePhase,phaseNumerator,primeEvaluate,Complex.ofReal_add,
    Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_natCast,he]
  exact numerator_spec _ _ _ _ _ _ hd

/-- The entire approximate prime sum has one explicitly known denominator. -/
theorem approximatePrimeSum_spec (b : ℕ) (D : PrimeData) (N : ℕ) :
    approximatePrimeSum b D N = embed (integerPrimeSum b D N)/(commonScale b:ℂ)^4 := by
  unfold approximatePrimeSum phaseSum integerPrimeSum
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
    phaseNumerator_spec b D d y (Nat.pos_of_mem_divisors hd),embed_nsmul]
  simp only [productNumerator,embed_multiply]
  ring

theorem rational_round (A : ℤ) (D : ℕ) (hD : 0<D) :
    ⌊(A:ℝ)/D+1/2⌋=(2*A+(D:ℤ))/(2*(D:ℤ)) := by
  have hd : (D:ℝ)≠0 := by exact_mod_cast hD.ne'
  have he : (A:ℝ)/D+1/2=((2*A+(D:ℤ):ℤ):ℝ)/((2*D:ℕ):ℝ) := by
    push_cast
    field_simp
  rw [he,Int.floor_div_natCast,Int.floor_intCast]
  simp

theorem integerResult_eq_round (b : ℕ) (D : PrimeData) (N : ℕ) :
    integerResult b D N = ⌊(approximatePrimeSum b D N).re+1/2⌋ := by
  rw [approximatePrimeSum_spec]
  have he : (embed (integerPrimeSum b D N)/(commonScale b:ℂ)^4).re =
      ((integerPrimeSum b D N).1:ℝ)/(commonScale b^4:ℕ) := by
    rw [show (commonScale b:ℂ)^4=(((commonScale b^4:ℕ):ℝ):ℂ) by
      simp only [Nat.cast_pow,Complex.ofReal_pow,Complex.ofReal_natCast]]
    simp only [Complex.div_ofReal_re,embed,Complex.add_re,Complex.intCast_re,
      Complex.mul_re,Complex.intCast_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_zero,add_zero]
  rw [he,rational_round _ _ (pow_pos (commonScale_pos b) 4)]
  simp only [integerResult,Nat.cast_pow]

/-- Pure integer division recovers the exact prime sum from any certified table. -/
theorem integerResult_eq_primeSum {N b : ℕ} {D : PrimeData}
    (hN : N ≤ 2^b) (hD : Certified b D) : integerResult b D N=(primeSum N:ℤ) := by
  rw [integerResult_eq_round]
  exact CertifiedPrimeSum.primeSum_round hN hD

theorem integerResult_all_inputs (N : ℕ) (D : PrimeData)
    (hD : Certified (Nat.log 2 N+1) D) :
    integerResult (Nat.log 2 N+1) D N=(primeSum N:ℤ) :=
  integerResult_eq_primeSum (Nat.lt_pow_succ_log_self (by decide) N).le hD

end PrimeAlgorithm.IntegerPrimeSum
