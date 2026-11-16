import PrimeIndependent.MainResults
import PrimeAlgorithm.PrimeSumMachine
import PrimeAlgorithm.PrimeCountMachine
import PrimeAlgorithm.PrimeFindingMachine

/-! The complete existing algorithms discharge the three independent Mathlib-only
specifications. Challenge is deliberately not imported. -/

namespace PrimeIndependent

theorem sumPrimes_eq (N : ℕ) : sumPrimes N = PrimeAlgorithm.primeSum N := by
  simp only [sumPrimes, PrimeAlgorithm.primeSum, Finset.sum_filter, id_eq]

theorem primeSum_time : ExactPrimeSum := by
  obtain ⟨M, C, hfinite, hrun⟩ := PrimeAlgorithm.PrimeSumMachine.primeSum_TM_all_inputs
  refine ⟨M, C, hfinite, fun N => ?_⟩
  rw [sumPrimes_eq]
  exact hrun N

theorem primeCounting_time : ExactPrimeCounting :=
  PrimeAlgorithm.PrimeCountMachine.primeCounting_TM_all_inputs

theorem primeFinding_time : ExactPrimeFinding := by
  obtain ⟨M, C, hfinite, hrun⟩ :=
    PrimeAlgorithm.PrimeFindingMachine.primeFinding_TM_all_inputs
  refine ⟨M, C, hfinite, fun N => ?_⟩
  exact ⟨PrimeAlgorithm.PrimeFindingMachine.findPrime N, hrun N⟩

end PrimeIndependent
