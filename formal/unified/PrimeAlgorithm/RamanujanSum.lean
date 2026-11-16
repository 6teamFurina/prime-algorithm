module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic

public section

namespace PrimeAlgorithm.Ramanujan

open Finset Polynomial
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

@[expose] noncomputable def primitiveSum : ArithmeticFunction ℂ := by
  classical
  exact ⟨fun n => ∑ z ∈ primitiveRoots n ℂ, z, by simp⟩

theorem primitiveSum_apply (n : ℕ) :
    primitiveSum n = ∑ z ∈ primitiveRoots n ℂ, z := rfl

theorem sum_nthRoots (n : ℕ) :
    (∑ z ∈ nthRootsFinset n (1 : ℂ), z) = if n = 1 then 1 else 0 := by
  classical
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  let : NeZero n := ⟨hn.ne'⟩
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn.ne'
  have himage : (range n).image (fun i => z ^ i) = nthRootsFinset n (1 : ℂ) := by
    ext w
    simp only [mem_image, mem_range, mem_nthRootsFinset hn]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [← pow_mul, mul_comm i, pow_mul, hz.pow_eq_one, one_pow]
    · exact hz.eq_pow_of_pow_eq_one
  rw [← himage, sum_image]
  · by_cases h : n = 1
    · simp [h]
    · rw [if_neg h]
      exact hz.geom_sum_eq_zero (by omega)
  · intro i hi j hj hij
    exact hz.pow_inj (mem_range.mp hi) (mem_range.mp hj) hij

theorem primitiveSum_mul_zeta : primitiveSum * ζ = (1 : ArithmeticFunction ℂ) := by
  classical
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply]
  simp_rw [primitiveSum_apply]
  rw [← sum_biUnion]
  · rw [← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    exact sum_nthRoots n
  · intro a ha b hb hab
    exact IsPrimitiveRoot.disjoint hab

theorem primitiveSum_eq_moebius : primitiveSum = (μ : ArithmeticFunction ℂ) := by
  calc
    primitiveSum = primitiveSum * (ζ * μ) := by simp
    _ = (primitiveSum * ζ) * μ := by rw [mul_assoc]
    _ = μ := by rw [primitiveSum_mul_zeta, one_mul]

theorem sum_primitiveRoots_eq_moebius (n : ℕ) :
    (∑ z ∈ primitiveRoots n ℂ, z) = (μ n : ℂ) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n) primitiveSum_eq_moebius
  simpa [primitiveSum_apply] using h

/-- The exact complex phase used by the arithmetic quotient network. -/
@[expose] noncomputable def phase (d x : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) / d))

theorem phase_eq_pow (d x : ℕ) :
    phase d x = Complex.exp (2 * Real.pi * Complex.I / d) ^ x := by
  rw [phase, ← Complex.exp_nat_mul]
  congr 1
  ring

@[simp] theorem norm_phase (d x : ℕ) : ‖phase d x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

/-- Ramanujan's finite identity, including d=0 (empty sum) and d=1 (x=0).
No cancellation estimate or asymptotic assumption is used. -/
theorem sum_coprime_phase_eq_moebius (d : ℕ) :
    (∑ x ∈ (range d).filter (fun x => x.Coprime d), phase d x) = (μ d : ℂ) := by
  classical
  rcases d.eq_zero_or_pos with rfl | hd
  · simp
  let : NeZero d := ⟨hd.ne'⟩
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
  have hz : IsPrimitiveRoot z d := Complex.isPrimitiveRoot_exp d hd.ne'
  calc
    (∑ x ∈ (range d).filter (fun x => x.Coprime d), phase d x) =
        ∑ w ∈ primitiveRoots d ℂ, w := by
      apply sum_bij (fun x _ => z ^ x)
      · intro x hx
        exact (mem_primitiveRoots hd).mpr (hz.pow_of_coprime x (mem_filter.mp hx).2)
      · intro x hx y hy hxy
        exact hz.pow_inj (mem_range.mp (mem_filter.mp hx).1)
          (mem_range.mp (mem_filter.mp hy).1) hxy
      · intro w hw
        obtain ⟨x, hx, hcop, hpow⟩ := hz.isPrimitiveRoot_iff.mp
          ((mem_primitiveRoots hd).mp hw)
        exact ⟨x, mem_filter.mpr ⟨mem_range.mpr hx, hcop⟩, hpow⟩
      · intro x hx
        exact phase_eq_pow d x
    _ = (μ d : ℂ) := sum_primitiveRoots_eq_moebius d

/-- The real cosine form, with no imaginary component left to evaluate. -/
theorem sum_coprime_cos_eq_moebius (d : ℕ) :
    (∑ x ∈ (range d).filter (fun x => x.Coprime d), (phase d x).re) = (μ d : ℝ) := by
  have h := congrArg Complex.re (sum_coprime_phase_eq_moebius d)
  simpa using h

/-- The exact finite convolution Λ = μ * log, written on actual divisors. -/
theorem vonMangoldt_divisor_sum (n : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      ∑ d ∈ n.divisors, (μ d : ℝ) * Real.log (n / d : ℕ) := by
  rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt, ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply]
  exact Nat.sum_divisorsAntidiagonal (fun d m => (μ d : ℝ) * Real.log m)

/-- Exact phase expansion of von Mangoldt; every sum is finite. -/
theorem vonMangoldt_phase_sum (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℂ) =
      ∑ d ∈ n.divisors, (∑ x ∈ (range d).filter (fun x => x.Coprime d), phase d x) *
        (Real.log (n / d : ℕ) : ℂ) := by
  rw [vonMangoldt_divisor_sum]
  push_cast
  apply sum_congr rfl
  intro d hd
  rw [sum_coprime_phase_eq_moebius]

/-- The weighted Λ/log sum is exactly a finite sum of the arithmetic phases.
This is an identity for every finite set of inputs, without convergence or
primality-oracle assumptions. Zero denominators use the field's division by
zero convention; the algorithm only applies it to n≥2. -/
theorem weighted_log_phase_sum (s : Finset ℕ) (k : ℕ) :
    (∑ n ∈ s, (n : ℂ) ^ k * (ArithmeticFunction.vonMangoldt n : ℂ) /
      (Real.log n : ℂ)) =
      ∑ n ∈ s, ∑ d ∈ n.divisors,
        ∑ x ∈ (range d).filter (fun x => x.Coprime d),
          ((n : ℂ) ^ k * (Real.log (n / d : ℕ) : ℂ) / (Real.log n : ℂ)) * phase d x := by
  apply sum_congr rfl
  intro n hn
  rw [vonMangoldt_phase_sum, mul_sum, sum_div]
  apply sum_congr rfl
  intro d hd
  rw [sum_mul, mul_sum, sum_div]
  apply sum_congr rfl
  intro x hx
  ring

/-- The exact number of phase witnesses over the divisor choices of one n.
In particular the absolute-error budget counts witnesses before cancellation. -/
theorem phase_witness_count (n : ℕ) :
    (∑ d ∈ n.divisors, ((range d).filter (fun x => x.Coprime d)).card) = n := by
  calc
    _ = ∑ d ∈ n.divisors, Nat.totient d := by
      apply sum_congr rfl
      intro d hd
      simp only [Nat.totient_eq_card_coprime, Nat.coprime_comm]
    _ = n := Nat.sum_totient n

theorem total_phase_witness_count (N : ℕ) :
    (∑ n ∈ range (N + 1),
      ∑ d ∈ n.divisors, ((range d).filter (fun x => x.Coprime d)).card) =
      ∑ n ∈ range (N + 1), n := by
  simp_rw [phase_witness_count]

theorem total_phase_witness_count_closed (N : ℕ) :
    (∑ n ∈ range (N + 1),
      ∑ d ∈ n.divisors, ((range d).filter (fun x => x.Coprime d)).card) =
      N * (N + 1) / 2 := by
  rw [total_phase_witness_count, Finset.sum_range_id]
  simp [Nat.mul_comm]

end PrimeAlgorithm.Ramanujan
