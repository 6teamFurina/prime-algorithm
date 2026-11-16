module

public import PrimeAlgorithm.RamanujanSum
public import PrimeAlgorithm.PhaseApproximation
public import PrimeAlgorithm.MoebiusPrimeIndicator
public import Mathlib.Tactic

public section

namespace PrimeAlgorithm.DoubleRamanujan

open Finset
open scoped ArithmeticFunction.Moebius
open PrimeAlgorithm.Ramanujan

@[expose] def unitsBelow (n : ℕ) : Finset ℕ :=
  (range n).filter (fun x => x.Coprime n)

@[expose] noncomputable def amplitude (n d x y : ℕ) : ℂ :=
  (Real.log (n / d : ℕ) : ℂ) / (Real.log n : ℂ) * phase n x * phase d y

@[expose] noncomputable def phaseSum (N : ℕ) (A : ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  -(∑ n ∈ Icc 2 N, ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
    ∑ y ∈ unitsBelow d, (n : ℂ) * A n d x y)

theorem mobius_vonMangoldt_phase (n : ℕ) :
    (μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) =
      ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ y ∈ unitsBelow d,
        (Real.log (n / d : ℕ) : ℂ) * phase n x * phase d y := by
  rw [← sum_coprime_phase_eq_moebius, vonMangoldt_phase_sum, sum_mul]
  apply sum_congr rfl
  intro x hx
  rw [mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [sum_mul, mul_sum]
  apply sum_congr rfl
  intro y hy
  ring

theorem weightedTerm_phase (n : ℕ) :
    -(n : ℂ) * (μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) =
      -(∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors, ∑ y ∈ unitsBelow d,
        (n : ℂ) * amplitude n d x y) := by
  calc
    _ = (-(n : ℂ) / (Real.log n : ℂ)) *
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

/-- Complete prime summation by a fixed number of Ramanujan variables.
There is no exponent-inversion loop or growing multiplication chain. -/
theorem primeSum_phase (N : ℕ) : (primeSum N : ℂ) = phaseSum N amplitude := by
  have h := congrArg (fun t : ℝ => (t : ℂ)) (primeSum_moebius_vonMangoldt N)
  simp only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_intCast] at h
  rw [h]
  have hrestrict : (∑ n ∈ range (N + 1),
      -(n : ℂ) * (μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)) =
      ∑ n ∈ Icc 2 N,
        -(n : ℂ) * (μ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ) := by
    symm
    apply sum_subset
    · intro n hn
      exact mem_range.mpr (by have := (mem_Icc.mp hn).2; omega)
    · intro n hn hnot
      have hnN : n ≤ N := by have := mem_range.mp hn; omega
      have hnsmall : n ≤ 1 := by
        have : ¬(2 ≤ n ∧ n ≤ N) := by simpa only [mem_Icc] using hnot
        omega
      interval_cases n <;> simp
  rw [hrestrict]
  simp_rw [weightedTerm_phase]
  simp only [phaseSum, sum_neg_distrib]

/-- Number of witnesses over one n, exactly before cancellation. -/
theorem witness_count (n : ℕ) :
    (∑ _x ∈ unitsBelow n, ∑ d ∈ n.divisors, (unitsBelow d).card) =
      (unitsBelow n).card * n := by
  simp [unitsBelow, phase_witness_count]

theorem unitsBelow_card_le (n : ℕ) : (unitsBelow n).card ≤ n := by
  exact (card_filter_le _ _).trans_eq (card_range n)

/-- Four-index amplitude errors are accumulated over actual arithmetic
witnesses. The final N⁴ bound includes the n weight and does not use cancellation. -/
theorem phaseSum_error (N : ℕ) (A B : ℕ → ℕ → ℕ → ℕ → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ n ∈ Icc 2 N, ∀ x ∈ unitsBelow n, ∀ d ∈ n.divisors,
      ∀ y ∈ unitsBelow d, ‖A n d x y - B n d x y‖ ≤ ε) :
    ‖phaseSum N A - phaseSum N B‖ ≤ (N : ℝ) ^ 4 * ε := by
  have hid : phaseSum N A - phaseSum N B =
      -(∑ n ∈ Icc 2 N, ∑ x ∈ unitsBelow n, ∑ d ∈ n.divisors,
        ∑ y ∈ unitsBelow d, (n : ℂ) * (A n d x y - B n d x y)) := by
    simp only [phaseSum, mul_sub, sum_sub_distrib, neg_sub_neg]
    ring
  have hlocal : ∀ n ∈ Icc 2 N, ∀ x ∈ unitsBelow n, ∀ d ∈ n.divisors,
      ∀ y ∈ unitsBelow d, ‖(n : ℂ) * (A n d x y - B n d x y)‖ ≤ (N : ℝ) * ε := by
    intro n hn x hx d hd y hy
    rw [norm_mul, Complex.norm_natCast]
    apply mul_le_mul
    · exact_mod_cast (mem_Icc.mp hn).2
    · exact herr n hn x hx d hd y hy
    · exact norm_nonneg _
    · positivity
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
        ∑ y ∈ unitsBelow d, ‖(n : ℂ) * (A n d x y - B n d x y)‖ := by
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

/-- Four separately approximated Cauchy factors have a polynomial condition
number: log amplitude L, inverse-log bound 2, and two unit phases. -/
theorem four_factor_error (A B C D a b c d : ℂ) (L δ : ℝ)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha : ‖a‖ ≤ L) (hb : ‖b‖ ≤ 2) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hA : ‖A - a‖ ≤ δ) (hB : ‖B - b‖ ≤ δ)
    (hC : ‖C - c‖ ≤ δ) (hD : ‖D - d‖ ≤ δ) :
    ‖A * B * C * D - a * b * c * d‖ ≤ (12 + 10 * L) * δ := by
  have hBn : ‖B‖ ≤ 3 := by
    have := norm_add_le (B - b) b
    rw [sub_add_cancel] at this
    linarith
  have hCn : ‖C‖ ≤ 2 := by
    have := norm_add_le (C - c) c
    rw [sub_add_cancel, hc] at this
    linarith
  have hDn : ‖D‖ ≤ 2 := by
    have := norm_add_le (D - d) d
    rw [sub_add_cancel, hd] at this
    linarith
  let t₁ := (A - a) * B * C * D
  let t₂ := a * (B - b) * C * D
  let t₃ := a * b * (C - c) * D
  let t₄ := a * b * c * (D - d)
  have ht₁ : ‖t₁‖ ≤ 12 * δ := by
    simp only [t₁, norm_mul]
    calc
      _ ≤ δ * 3 * 2 * 2 := by gcongr
      _ = _ := by ring
  have ht₂ : ‖t₂‖ ≤ 4 * L * δ := by
    simp only [t₂, norm_mul]
    calc
      _ ≤ L * δ * 2 * 2 := by gcongr
      _ = _ := by ring
  have ht₃ : ‖t₃‖ ≤ 4 * L * δ := by
    simp only [t₃, norm_mul]
    calc
      _ ≤ L * 2 * δ * 2 := by gcongr
      _ = _ := by ring
  have ht₄ : ‖t₄‖ ≤ 2 * L * δ := by
    simp only [t₄, norm_mul, hc, mul_one]
    calc
      _ ≤ L * 2 * δ := by gcongr
      _ = _ := by ring
  have hid : A * B * C * D - a * b * c * d = t₁ + t₂ + t₃ + t₄ := by
    dsimp [t₁, t₂, t₃, t₄]
    ring
  rw [hid]
  have h12 := norm_add_le t₁ t₂
  have h123 := norm_add_le (t₁ + t₂) t₃
  have h1234 := norm_add_le (t₁ + t₂ + t₃) t₄
  nlinarith

theorem log_divisor_norm_le {n d b : ℕ} (hd : d ∈ n.divisors) (hn : n ≤ 2 ^ b) :
    ‖(Real.log (n / d : ℕ) : ℂ)‖ ≤ (b : ℝ) := by
  have hdp : 0 < d := Nat.pos_of_mem_divisors hd
  have hnp : 0 < n := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd)
  have hmp : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnp (Nat.dvd_of_mem_divisors hd)) hdp
  have hm1 : (1 : ℝ) ≤ (n / d : ℕ) := by exact_mod_cast hmp
  have hmb : ((n / d : ℕ) : ℝ) ≤ (2 : ℝ) ^ b := by
    exact_mod_cast (Nat.div_le_self n d).trans hn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hm1)]
  calc
    _ ≤ Real.log ((2 : ℝ) ^ b) := Real.log_le_log (by linarith) hmb
    _ = (b : ℝ) * Real.log 2 := Real.log_pow 2 b
    _ ≤ (b : ℝ) := by
      have hl : Real.log 2 ≤ 1 := by
        have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at ht
        exact ht
      have := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ b by positivity)
      simpa using this

theorem inverse_log_norm_le {n : ℕ} (hn : 2 ≤ n) :
    ‖(1 : ℂ) / (Real.log n : ℂ)‖ ≤ 2 := by
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht
    exact ht
  have hln : (1 / 2 : ℝ) ≤ Real.log n :=
    hl2.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ Real.log n)]
  apply (div_le_iff₀ (by linarith : 0 < Real.log n)).mpr
  linarith

/-- Directly usable with the four rational Cauchy approximations in the
constant-arity version of the algorithm. -/
theorem amplitude_error {n d b : ℕ} (x y : ℕ) (F G H K : ℂ) (δ : ℝ)
    (hn : 2 ≤ n) (hnb : n ≤ 2 ^ b) (hd : d ∈ n.divisors)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hF : ‖F - (Real.log (n / d : ℕ) : ℂ)‖ ≤ δ)
    (hG : ‖G - (1 : ℂ) / (Real.log n : ℂ)‖ ≤ δ)
    (hH : ‖H - phase n x‖ ≤ δ) (hK : ‖K - phase d y‖ ≤ δ) :
    ‖F * G * H * K - amplitude n d x y‖ ≤ (12 + 10 * (b : ℝ)) * δ := by
  simpa only [amplitude, div_eq_mul_inv, one_mul] using
    four_factor_error F G H K (Real.log (n / d : ℕ) : ℂ)
      ((1 : ℂ) / (Real.log n : ℂ)) (phase n x) (phase d y) b δ
      (by positivity) hδ hδ1 (log_divisor_norm_le hd hnb) (inverse_log_norm_le hn)
      (norm_phase n x) (norm_phase d y) hF hG hH hK

theorem phaseSum_round (N : ℕ) (A : ℕ → ℕ → ℕ → ℕ → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ n ∈ Icc 2 N, ∀ x ∈ unitsBelow n, ∀ d ∈ n.divisors,
      ∀ y ∈ unitsBelow d, ‖A n d x y - amplitude n d x y‖ ≤ ε)
    (hsmall : (N : ℝ) ^ 4 * ε < 1 / 2) :
    ⌊(phaseSum N A).re + 1 / 2⌋ = (primeSum N : ℤ) := by
  apply PhaseApproximation.floor_add_half_eq
  have h := phaseSum_error N A amplitude ε hε herr
  rw [← primeSum_phase] at h
  have hr := (Complex.abs_re_le_norm (phaseSum N A - (primeSum N : ℂ))).trans h
  simpa using hr.trans_lt hsmall

/-- A concrete dyadic target for each of the four component approximations. -/
@[expose] noncomputable def componentTolerance (b : ℕ) : ℝ :=
  1 / (64 * ((2 : ℝ) ^ b) ^ 6)

theorem componentTolerance_dyadic (b : ℕ) :
    componentTolerance b = 1 / (2 : ℝ) ^ (6 * b + 6) := by
  unfold componentTolerance
  rw [show 6 * b + 6 = b * 6 + 6 by omega, pow_add, pow_mul]
  ring

theorem componentTolerance_nonneg (b : ℕ) : 0 ≤ componentTolerance b := by
  unfold componentTolerance
  positivity

theorem componentTolerance_le_one (b : ℕ) : componentTolerance b ≤ 1 := by
  have ht : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have ht6 : (1 : ℝ) ≤ ((2 : ℝ) ^ b) ^ 6 := one_le_pow₀ ht
  unfold componentTolerance
  apply (div_le_one (by positivity)).mpr
  linarith

theorem precision_budget {N b : ℕ} (hN : N ≤ 2 ^ b) :
    (N : ℝ) ^ 4 * (12 + 10 * (b : ℝ)) * componentTolerance b < 1 / 2 := by
  let t : ℝ := 2 ^ b
  have ht : 1 ≤ t := one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by positivity
  have hb : (b : ℝ) ≤ t := by
    change (b : ℝ) ≤ (2 : ℝ) ^ b
    exact_mod_cast (Nat.lt_two_pow_self (n := b)).le
  have hNr : (N : ℝ) ≤ t := by
    change (N : ℝ) ≤ (2 : ℝ) ^ b
    exact_mod_cast hN
  have hL : 12 + 10 * (b : ℝ) ≤ 22 * t := by linarith
  have hδ := componentTolerance_nonneg b
  calc
    _ ≤ t ^ 4 * (22 * t) * componentTolerance b := by gcongr
    _ = (22 / 64 : ℝ) / t := by
      change t ^ 4 * (22 * t) * (1 / (64 * t ^ 6)) = _
      field_simp
    _ ≤ 22 / 64 := div_le_self (by norm_num) ht
    _ < 1 / 2 := by norm_num

/-- Local error contracts for log, inverse log and the two phase evaluations
suffice to recover primeSum exactly, with the explicit tolerance above.
Constructing the actual Cauchy approximants is a separate proof obligation. -/
theorem primeSum_round_of_components (N b : ℕ) (hN : N ≤ 2 ^ b)
    (F : ℕ → ℕ → ℂ) (G : ℕ → ℂ) (E : ℕ → ℕ → ℂ)
    (hF : ∀ n ∈ Icc 2 N, ∀ d ∈ n.divisors,
      ‖F n d - (Real.log (n / d : ℕ) : ℂ)‖ ≤ componentTolerance b)
    (hG : ∀ n ∈ Icc 2 N,
      ‖G n - (1 : ℂ) / (Real.log n : ℂ)‖ ≤ componentTolerance b)
    (hE : ∀ d ∈ Icc 1 N, ∀ x ∈ unitsBelow d,
      ‖E d x - phase d x‖ ≤ componentTolerance b) :
    ⌊(phaseSum N (fun n d x y => F n d * G n * E n x * E d y)).re + 1 / 2⌋ =
      (primeSum N : ℤ) := by
  apply phaseSum_round N _ ((12 + 10 * (b : ℝ)) * componentTolerance b)
  · exact mul_nonneg (by positivity) (componentTolerance_nonneg b)
  · intro n hn x hx d hd y hy
    have hn2 := (mem_Icc.mp hn).1
    have hnN := (mem_Icc.mp hn).2
    apply amplitude_error x y _ _ _ _ _ hn2 (hnN.trans hN) hd
      (componentTolerance_nonneg b) (componentTolerance_le_one b)
      (hF n hn d hd) (hG n hn)
    · exact hE n (mem_Icc.mpr ⟨by omega, hnN⟩) x hx
    · have hdp : 0 < d := Nat.pos_of_mem_divisors hd
      have hdn : d ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)
      exact hE d (mem_Icc.mpr ⟨hdp, hdn.trans hnN⟩) y hy
  · simpa only [mul_assoc] using precision_budget hN

end PrimeAlgorithm.DoubleRamanujan
