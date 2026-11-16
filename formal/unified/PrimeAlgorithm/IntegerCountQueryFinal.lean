import PrimeAlgorithm.CountWitnessReindex
import PrimeAlgorithm.PrimeCountInteger

set_option maxHeartbeats 1000000
noncomputable section
namespace PrimeAlgorithm.IntegerCountQueryFinal
open Finset CertifiedCauchy CertifiedPrimeSum CertifiedNumerator IntegerPrimeSum PrimeCountInteger
  IntegerKernelExpansion CountQueryExpansion CountWitnessReindex DoubleRamanujan
  EthFollowup.Primes.CountKernel

abbrev QueryIndex (b : ℕ) :=
  Fin (b+1) × Fin (b+1) × Bool × NodeChoices b × (Fin 4 → Bool)

def queryParameters (b N : ℕ) (D : PrimeData) (q : QueryIndex b) : Parameters :=
  parameters b N q.1 q.2.1 D q.2.2.2.1

def branch (b : ℕ) (q : QueryIndex b) : Branch :=
  queryBranch q.2.2.1 q.2.2.2.1 q.2.2.2.2

def coefficient (b : ℕ) (D : PrimeData) (q : QueryIndex b) : GaussianInt :=
  -queryCoefficient b q.1 q.2.1 D q.2.2.2.1 q.2.2.2.2

def count (b N : ℕ) (D : PrimeData) (q : QueryIndex b) : ℕ :=
  queryCount b N q.1 q.2.1 D q.2.2.2.1 q.2.2.2.2 q.2.2.1

def queryNumerator (b N : ℕ) (D : PrimeData) : GaussianInt :=
  ∑q:QueryIndex b,coefficient b D q*(count b N D q:GaussianInt)

def queryResult (b N : ℕ) (D : PrimeData) : ℤ :=
  (2*(queryNumerator b N D).re+(commonScale b:ℤ)^4)/(2*(commonScale b:ℤ)^4)

theorem queryIndex_card (b : ℕ) :
    Fintype.card (QueryIndex b)=KernelSumExpansion.queryBound b := by
  simp only [QueryIndex,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    NodeChoices,
    Fintype.card_fun,NodeChoice,KernelSumExpansion.queryBound]
  ring

theorem productNumerator_zero {b n d x y : ℕ} {D : PrimeData} (h : n/d<2) :
    productNumerator b D n d x y=0 := by
  simp [productNumerator,logNumerator,h,multiply]

theorem integerPrimeCount_bins {N b : ℕ} (hN : N≤2^b) (D : PrimeData) :
    gaussian (integerPrimeCount b D N) =
      -(∑jM∈range (b+1),∑jN∈range (b+1),∑unitD:Bool,
        binNumerator b N jM jN D unitD) := by
  let F : Base→GaussianInt := fun v=>
    gaussian (productNumerator b D (v 0) (v 1) (v 3) (v 4))
  have hf : (∑n∈Icc 2 N,∑x∈unitsBelow n,∑d∈n.divisors,
      ∑y∈unitsBelow d,gaussian (productNumerator b D n d x y)) =
      ∑n∈Icc 2 N,∑x∈unitsBelow n,∑d∈n.divisors.filter (fun d=>2≤n/d),
        ∑y∈unitsBelow d,F ![n,d,n/d,x,y] := by
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro x hx
    change (∑d∈n.divisors,∑y∈unitsBelow d,gaussian (productNumerator b D n d x y)) =
      ∑d∈n.divisors.filter (fun d=>2≤n/d),∑y∈unitsBelow d,
        gaussian (productNumerator b D n d x y)
    symm
    apply sum_subset (filter_subset _ _)
    intro d hd hnot
    have hsmall : n/d<2 := by
      have hh : ¬2≤n/d := by intro h; exact hnot (mem_filter.mpr ⟨hd,h⟩)
      omega
    simp only [productNumerator_zero hsmall,gaussian_zero,sum_const_zero]
  simp only [integerPrimeCount,gaussian_neg,gaussian_sum]
  rw [hf,original_sum N F,sum_bins hN F]
  apply congrArg (fun z : GaussianInt => -z)
  apply sum_congr rfl
  intro jM _
  apply sum_congr rfl
  intro jN _
  apply sum_congr rfl
  intro unitD _
  exact (binNumerator_eq_actual b N jM jN D unitD).symm

/-- The actual integer numerator of the analytic prime-count formula is a
polynomial-sized weighted sum of the concrete four-kernel descriptor counts. -/
theorem integerPrimeCount_eq_queries {N b : ℕ} {D : PrimeData}
    (hN : N≤2^b) (hD : Certified b D) :
    gaussian (integerPrimeCount b D N)=queryNumerator b N D := by
  rw [integerPrimeCount_bins hN D]
  simp_rw [bin_expansion hD]
  unfold queryNumerator
  simp only [QueryIndex,Fintype.sum_prod_type,coefficient,count]
  simp only [←Fin.sum_univ_eq_sum_range]
  simp only [neg_mul,sum_neg_distrib]

theorem queryResult_eq_integerResult {N b : ℕ} {D : PrimeData}
    (hN : N≤2^b) (hD : Certified b D) : queryResult b N D=PrimeCountInteger.integerResult b D N := by
  unfold queryResult PrimeCountInteger.integerResult
  rw [←integerPrimeCount_eq_queries hN hD]
  rfl

theorem queryResult_eq_primeCounting {N b : ℕ} {D : PrimeData}
    (hN : N≤2^b) (hD : Certified b D) : queryResult b N D=(Nat.primeCounting N:ℤ) := by
  rw [queryResult_eq_integerResult hN hD]
  exact integerResult_eq_primeCounting hN hD

theorem queryResult_all_inputs (N : ℕ) (D : PrimeData)
    (hD : Certified (Nat.log 2 N+1) D) :
    queryResult (Nat.log 2 N+1) N D=(Nat.primeCounting N:ℤ) :=
  queryResult_eq_primeCounting (Nat.lt_pow_succ_log_self (by decide) N).le hD

end PrimeAlgorithm.IntegerCountQueryFinal
