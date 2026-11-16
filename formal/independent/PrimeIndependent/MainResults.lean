import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Nat.Bits
import Mathlib.NumberTheory.PrimeCounting

/-!
# Independent statements of exact prime summation, counting and finding

This file imports Mathlib alone. It contains definitions, not proofs, and does
not import any definition from the counting engine or from PrimeAlgorithm.
It is the mathematical specification to read independently of those proofs.

`sumPrimes N` is the sum of all natural primes p <= N. The second output is
Mathlib's `Nat.primeCounting N`, the number of primes p <= N. Inputs and outputs
use Mathlib's `Nat.bits`: least significant bit first; zero is the empty list.
The third statement outputs a prime p with N < p <= 2 * max N 1, so positive
inputs have N < p <= 2*N and zero is handled as well. It specifies the output
property directly, without importing the implementation's search function.

A machine is Mathlib's deterministic multi-stack Turing machine. All of its
stack alphabets must be finite. `Outputs` directly uses Mathlib's timed halting
relation, with the input/output alphabet bijections supplied by the machine.
Thus the meanings of output, time and finiteness do not come from the proof.

Each statement chooses one machine and one natural constant C before N. All
natural inputs, including zero and one, are covered. The running time is
floor(C * 2^(C*b/sqrt(log_2(b+2)))), where b is the original input's binary
length. The three statements can use different machines and constants.
-/

namespace PrimeIndependent

/-- The exact sum of all primes at most N, specified independently as a finite sum. -/
def sumPrimes (N : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (N + 1), if Nat.Prime p then p else 0

/-- The common form of the complete machine time bound. -/
noncomputable def timeBound (C N : ℕ) : ℕ :=
  ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * (Nat.bits N).length /
    Real.sqrt (Real.logb 2 ((Nat.bits N).length + 2)))⌋₊

/-- Started with x, halt within t steps with exactly y on the output stack.
The semantics are Mathlib's; other stacks are empty and the internal state is
restored as required by `TM2OutputsInTime`. -/
def Outputs (M : Turing.TM2ComputableAux Bool Bool)
    (x y : List Bool) (t : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
    (some (y.map M.outputAlphabet.invFun)) t)

/-- One fixed deterministic finite-alphabet machine computes the full prime sum. -/
def ExactPrimeSum : Prop :=
  ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ N : ℕ, Outputs M (Nat.bits N) (Nat.bits (sumPrimes N)) (timeBound C N)

/-- One fixed deterministic finite-alphabet machine computes the full prime count. -/
def ExactPrimeCounting : Prop :=
  ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ N : ℕ, Outputs M (Nat.bits N) (Nat.bits (Nat.primeCounting N)) (timeBound C N)

/-- One fixed deterministic finite-alphabet machine finds a prime above every N.
The witness p is constrained independently of the search implementation. -/
def ExactPrimeFinding : Prop :=
  ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
    (∀ i, Finite (M.tm.Γ i)) ∧
    ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ p ≤ 2 * max N 1 ∧
      Outputs M (Nat.bits N) (Nat.bits p) (timeBound C N)

end PrimeIndependent
