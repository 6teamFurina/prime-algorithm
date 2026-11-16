import PrimeAlgorithm.CertifiedNumerator
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Exact expansion of four sums of signed integer kernels into nonnegative
counting queries. The number of components is fixed at four. -/

namespace PrimeAlgorithm.KernelSumExpansion
open Finset

variable {I W : Type*} [Fintype I]

def signedValue (negative : Bool) (q : ℕ) : ℤ := if negative then -(q:ℤ) else q

def signProduct (σ : Fin 4 → Bool) : ℤ :=
  ∏ i, if σ i then (-1:ℤ) else 1

def count (s : Finset W) (weight : W → ℕ) (q : Fin 4 → W → ℕ)
    (negative : W → Fin 4 → Bool) (σ : Fin 4 → Bool) : ℕ :=
  ∑ w ∈ s.filter (fun w => negative w = σ), weight w * ∏ i, q i w

theorem signed_product (q : Fin 4 → ℕ) (σ : Fin 4 → Bool) :
    (∏ i, signedValue (σ i) (q i)) = signProduct σ * (∏ i, q i : ℕ) := by
  unfold signedValue signProduct
  rw [Nat.cast_prod, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  cases σ i <;> simp

theorem signed_count_expansion (s : Finset W) (weight : W → ℕ)
    (q : Fin 4 → W → ℕ) (negative : W → Fin 4 → Bool) :
    (∑ w ∈ s, (weight w : ℤ) * ∏ i, signedValue (negative w i) (q i w)) =
      ∑ σ : Fin 4 → Bool, signProduct σ * (count s weight q negative σ : ℤ) := by
  classical
  simp only [count, Nat.cast_sum, Nat.cast_mul, Nat.cast_prod, sum_filter,
    Nat.cast_ite, Nat.cast_zero]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _hw
  rw [signed_product]
  simp only [Nat.cast_prod]
  rw [show (∑ σ : Fin 4 → Bool,
      signProduct σ * (if negative w = σ then (weight w:ℤ) * ∏ i, (q i w:ℤ) else 0)) =
      signProduct (negative w) * ((weight w:ℤ) * ∏ i, (q i w:ℤ)) by simp]
  ring

def queryCoefficient (coefficient : Fin 4 → I → GaussianInt)
    (indices : Fin 4 → I) : GaussianInt := ∏ i, coefficient i (indices i)

def signedCount (s : Finset W) (weight : W → ℕ)
    (kernel : Fin 4 → I → W → ℤ) (indices : Fin 4 → I) : ℤ :=
  ∑ w ∈ s, (weight w:ℤ) * ∏ i, kernel i (indices i) w

theorem four_sum_expansion (s : Finset W) (weight : W → ℕ)
    (coefficient : Fin 4 → I → GaussianInt) (kernel : Fin 4 → I → W → ℤ) :
    (∑ w ∈ s, (weight w:GaussianInt) *
      ∏ i, ∑ j, coefficient i j * (kernel i j w:GaussianInt)) =
      ∑ indices : Fin 4 → I, queryCoefficient coefficient indices *
        (signedCount s weight kernel indices:GaussianInt) := by
  classical
  simp_rw [Fintype.prod_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro indices _
  simp only [queryCoefficient, signedCount, Int.cast_sum, Int.cast_mul,
    Int.cast_prod, Int.cast_natCast, mul_sum]
  apply sum_congr rfl
  intro w _
  rw [prod_mul_distrib]
  ring

/-- The partition may be the horizontal sign needed by the arithmetic
descriptor even when the selected component is imaginary. Its contribution
to the external Gaussian coefficient is allowed to depend on that partition. -/
theorem four_partitioned_expansion (s : Finset W) (weight : W → ℕ)
    (coefficient : Fin 4 → I → Bool → GaussianInt)
    (q : Fin 4 → I → W → ℕ) (branch : Fin 4 → I → W → Bool) :
    (∑ w ∈ s, (weight w:GaussianInt) *
      ∏ i, ∑ j, coefficient i j (branch i j w) * (q i j w:GaussianInt)) =
      ∑ indices : Fin 4 → I, ∑ σ : Fin 4 → Bool,
        (∏ i, coefficient i (indices i) (σ i)) *
          (count s weight (fun i w => q i (indices i) w)
            (fun w i => branch i (indices i) w) σ : GaussianInt) := by
  classical
  simp_rw [Fintype.prod_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro indices _
  simp only [count, Nat.cast_sum, sum_filter, Nat.cast_ite, Nat.cast_mul,
    Nat.cast_prod, Nat.cast_zero]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _hw
  rw [prod_mul_distrib]
  simp only [mul_ite, mul_zero]
  simp <;> ring

theorem query_count (M : ℕ) : Fintype.card (Fin 4 → Fin M × Bool) = (2*M)^4 := by
  simp [Fintype.card_fun, Fintype.card_prod, Nat.mul_comm]

theorem sign_count : Fintype.card (Fin 4 → Bool) = 16 := by decide

def queryBound (b : ℕ) : ℕ :=
  2*(b+1)^2*(2*CertifiedCauchy.nodeCount b)^4*16

theorem queryBound_polynomial (b : ℕ) : queryBound b ≤
    (32*370^4)*(b+2)^6 := by
  have hm : CertifiedCauchy.nodeCount b ≤ 185*(b+2) := by
    unfold CertifiedCauchy.nodeCount Cauchy.primeNodes
    omega
  have hi : b+1 ≤ b+2 := by omega
  unfold queryBound
  calc
    _ ≤ 2*(b+2)^2*(2*(185*(b+2)))^4*16 := by gcongr
    _ = _ := by ring

end PrimeAlgorithm.KernelSumExpansion
