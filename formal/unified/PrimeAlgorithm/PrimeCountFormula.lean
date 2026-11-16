import PrimeAlgorithm.CertifiedPrimeSum
import Mathlib.NumberTheory.PrimeCounting

/-! The unweighted four-kernel formula for exact prime counting. The same
certified coefficients and conservative error budget used for prime sums suffice. -/

noncomputable section
namespace PrimeAlgorithm.PrimeCountFormula
open Finset DoubleRamanujan CertifiedPrimeSum Ramanujan
open scoped ArithmeticFunction.Moebius

theorem primeCounting_eq_sum (N : ℕ) :
    Nat.primeCounting N = ∑ n ∈ range (N+1), if n.Prime then 1 else 0 := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  simp [Nat.primesBelow]

def phaseCount (N : ℕ) (A : ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  -(∑ n ∈ Icc 2 N, ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
    ∑ y ∈ unitsBelow d, A n d x y)

theorem term_phase (n : ℕ) :
    -(μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) =
      -(∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ y ∈ unitsBelow d,
        amplitude n d x y) := by
  calc
    _ = (-1 / (Real.log n : ℂ)) *
        ((μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) := by ring
    _ = _ := by
      rw [mobius_vonMangoldt_phase]
      simp only [mul_sum, ← sum_neg_distrib]
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro y hy
      simp only [amplitude]
      ring

theorem primeCounting_phase (N : ℕ) : (Nat.primeCounting N : ℂ) = phaseCount N amplitude := by
  have hterm (n : ℕ) :
      -(μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) =
        if n.Prime then 1 else 0 := by
    have h := congrArg (fun t : ℝ => (t : ℂ)) (moebius_vonMangoldt_primeIndicator n)
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_intCast, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using h
  have he : (Nat.primeCounting N : ℂ) = ∑ n ∈ range (N+1),
      -(μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) := by
    rw [primeCounting_eq_sum]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, hterm]
  rw [he]
  have hrestrict : (∑ n ∈ range (N+1),
      -(μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)) =
      ∑ n ∈ Icc 2 N,
        -(μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) := by
    symm
    apply sum_subset
    · intro n hn
      exact mem_range.mpr (by have := (mem_Icc.mp hn).2; omega)
    · intro n hn hnot
      have hnN : n≤N := by have := mem_range.mp hn; omega
      have hnsmall : n≤1 := by
        have : ¬(2≤n ∧ n≤N) := by simpa only [mem_Icc] using hnot
        omega
      interval_cases n <;> simp
  rw [hrestrict]
  simp_rw [term_phase]
  simp only [phaseCount, sum_neg_distrib]

theorem phaseCount_error (N : ℕ) (A B : ℕ → ℕ → ℕ → ℕ → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ n ∈ Icc 2 N, ∀ x ∈ unitsBelow n, ∀ d ∈ n.divisors,
      ∀ y ∈ unitsBelow d, ‖A n d x y - B n d x y‖ ≤ ε) :
    ‖phaseCount N A - phaseCount N B‖ ≤ (N : ℝ) ^ 4 * ε := by
  have hid : phaseCount N A - phaseCount N B =
      -(∑ n ∈ Icc 2 N, ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
        ∑ y ∈ unitsBelow d, (A n d x y - B n d x y)) := by
    simp only [phaseCount, sum_sub_distrib, neg_sub_neg]
    ring
  have hlocal : ∀ n ∈ Icc 2 N, ∀ x ∈ unitsBelow n, ∀ d ∈ n.divisors,
      ∀ y ∈ unitsBelow d, ‖(A n d x y - B n d x y)‖ ≤ (N : ℝ) * ε := by
    intro n hn x hx d hd y hy
    apply (herr n hn x hx d hd y hy).trans
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1≤N by have := mem_Icc.mp hn; omega)
    simpa using mul_le_mul_of_nonneg_right hN hε
  have hcount : ∀ n ∈ Icc 2 N,
      (∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ _y ∈ unitsBelow d, (N : ℝ) * ε) ≤
        (N : ℝ) ^ 3 * ε := by
    intro n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hcn : ((unitsBelow n).card : ℝ) ≤ n := by exact_mod_cast unitsBelow_card_le n
    have hc : ((unitsBelow n).card : ℝ) ≤ N := hcn.trans hnN
    have heq : (∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
        ∑ _y ∈ unitsBelow d, (N : ℝ) * ε) =
        ((unitsBelow n).card : ℝ) * (n : ℝ) * ((N : ℝ) * ε) := by
      simp only [sum_const, nsmul_eq_mul]
      rw [← sum_mul, ← Nat.cast_sum]
      change ((unitsBelow n).card : ℝ) *
        (((∑ d ∈ n.divisors, ((range d).filter (fun x => x.Coprime d)).card : ℕ) : ℝ) *
        ((N : ℝ) * ε)) = _
      rw [phase_witness_count]
      ring
    rw [heq]
    calc
      _ ≤ (N : ℝ) * N * (N * ε) := by gcongr
      _ = _ := by ring
  rw [hid, norm_neg]
  calc
    _ ≤ ∑ n ∈ Icc 2 N, ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
        ∑ y ∈ unitsBelow d, ‖(A n d x y - B n d x y)‖ := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro x hx
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro d hd
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 2 N, ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
        ∑ _y ∈ unitsBelow d, (N : ℝ) * ε := by
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro x hx
      apply sum_le_sum
      intro d hd
      exact sum_le_sum (fun y hy => hlocal n hn x hx d hd y hy)
    _ ≤ ∑ _n ∈ Icc 2 N, (N : ℝ) ^ 3 * ε := sum_le_sum hcount
    _ ≤ (N : ℝ) * ((N : ℝ) ^ 3 * ε) := by
      simp only [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show (Icc 2 N).card ≤ N by simp [Nat.card_Icc])
    _ = _ := by ring

theorem phaseCount_round (N : ℕ) (A : ℕ → ℕ → ℕ → ℕ → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ n ∈ Icc 2 N, ∀ x ∈ unitsBelow n, ∀ d ∈ n.divisors,
      ∀ y ∈ unitsBelow d, ‖A n d x y - amplitude n d x y‖ ≤ ε)
    (hsmall : (N : ℝ)^4 * ε < 1/2) :
    ⌊(phaseCount N A).re+1/2⌋ = (Nat.primeCounting N : ℤ) := by
  apply PhaseApproximation.floor_add_half_eq
  have h := phaseCount_error N A amplitude ε hε herr
  rw [← primeCounting_phase] at h
  have hr := (Complex.abs_re_le_norm (phaseCount N A - (Nat.primeCounting N : ℂ))).trans h
  simpa using hr.trans_lt hsmall

def approximatePrimeCount (b : ℕ) (D : PrimeData) (N : ℕ) : ℂ :=
  phaseCount N (fun n d x y => approximateLog b D (n/d) * approximateInvLog b D n *
    approximatePhase b D n x * approximatePhase b D d y)

theorem primeCounting_round {N b : ℕ} {D : PrimeData}
    (hN : N≤2^b) (hD : Certified b D) :
    ⌊(approximatePrimeCount b D N).re+1/2⌋ = (Nat.primeCounting N : ℤ) := by
  apply phaseCount_round N _ ((12+10*(b:ℝ))*componentTolerance b)
  · exact mul_nonneg (by positivity) (componentTolerance_nonneg b)
  · intro n hn x hx d hd y hy
    have hn2 := (mem_Icc.mp hn).1
    have hnN := (mem_Icc.mp hn).2
    apply amplitude_error x y _ _ _ _ _ hn2 (hnN.trans hN) hd
      (componentTolerance_nonneg b) (componentTolerance_le_one b)
    · exact log_accuracy hD ((Nat.div_le_self n d).trans (hnN.trans hN))
    · exact invLog_accuracy hD hn2 (hnN.trans hN)
    · exact phase_accuracy hD (by omega) (mem_range.mp (mem_filter.mp hx).1)
    · exact phase_accuracy hD (Nat.pos_of_mem_divisors hd) (mem_range.mp (mem_filter.mp hy).1)
  · simpa only [mul_assoc] using precision_budget hN

theorem primeCounting_all_inputs (N : ℕ) (D : PrimeData)
    (hD : Certified (Nat.log 2 N+1) D) :
    ⌊(approximatePrimeCount (Nat.log 2 N+1) D N).re+1/2⌋ = (Nat.primeCounting N : ℤ) :=
  primeCounting_round (Nat.lt_pow_succ_log_self (by decide) N).le hD

end PrimeAlgorithm.PrimeCountFormula
