import PrimeAlgorithm.CauchyAnalytic
import PrimeAlgorithm.CauchyPrecision
import PrimeAlgorithm.DoubleRamanujan

/-! Actual analytic Cauchy sums, including the m=1 branch, recover primeSum.
An explicit node count linear in the bit length supplies every accuracy bound;
the evaluator is defined here, rather than supplied as an approximation oracle.
Rational coefficient quantization and the counting-machine implementation are
separate obligations. -/

noncomputable section
namespace PrimeAlgorithm.CauchyPrimeSum

open Finset PrimeAlgorithm.Cauchy PrimeAlgorithm.DoubleRamanujan

def mantissa (n : ℕ) : ℝ := (n : ℝ) / (2 : ℝ) ^ Nat.log 2 n

theorem mantissa_interval {n : ℕ} (hn : 0 < n) : mantissa n ∈ Set.Icc 1 2 := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n := by positivity
  have hl : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have hu : (n : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 n := by
    have h : n < 2 * 2 ^ Nat.log 2 n := by
      simpa only [pow_succ, mul_comm] using
        Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
    exact_mod_cast h
  constructor
  · exact (one_le_div hp).mpr hl
  · exact (div_le_iff₀ hp).mpr hu.le

theorem normalized_log {n : ℕ} (hn : 0 < n) :
    logAmplitude (Nat.log 2 n) (mantissa n) = (Real.log n : ℂ) := by
  have hm : 0 < mantissa n := by unfold mantissa; positivity
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hreal : (Nat.log 2 n : ℝ) * Real.log 2 + Real.log (mantissa n) = Real.log n := by
    unfold mantissa
    rw [Real.log_div hnr (by positivity), Real.log_pow]
    ring
  have hc := congrArg (fun t : ℝ => (t : ℂ)) hreal
  simpa only [logAmplitude, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_log hm.le] using hc

theorem normalized_invLog {n : ℕ} (hn : 0 < n) :
    invLogAmplitude (Nat.log 2 n) (mantissa n) = (1 : ℂ) / (Real.log n : ℂ) := by
  rw [invLogAmplitude, normalized_log hn, one_div]

def approximateLog (M n : ℕ) : ℂ :=
  if n < 2 then 0 else cauchyApprox M (logAmplitude (Nat.log 2 n)) (mantissa n)

def approximateInvLog (M n : ℕ) : ℂ :=
  cauchyApprox M (invLogAmplitude (Nat.log 2 n)) (mantissa n)

def approximatePhase (M d x : ℕ) : ℂ :=
  cauchyApprox M shiftedPhase ((1 + (x : ℝ) / d : ℝ) : ℂ)

theorem approximateLog_error {M b n : ℕ} (hM : 0 < M) (hn : n ≤ 2 ^ b) :
    ‖approximateLog M n - (Real.log n : ℂ)‖ ≤
      49 * ((b : ℝ) + 6) * (6 / 7 : ℝ) ^ M := by
  by_cases hs : n < 2
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp [approximateLog] <;> positivity
  · have hnp : 0 < n := by omega
    have hj : Nat.log 2 n ≤ b := by
      have h := Nat.log_mono_right (b := 2) hn
      simpa only [Nat.log_pow (by decide : 1 < 2)] using h
    have h := cauchyApprox_log_error hM (Nat.log 2 n) (mantissa_interval hnp)
    rw [normalized_log hnp] at h
    rw [approximateLog, if_neg hs]
    exact h.trans (by gcongr)

theorem approximateInvLog_error {M n : ℕ} (hM : 0 < M) (hn : 2 ≤ n) :
    ‖approximateInvLog M n - (1 : ℂ) / (Real.log n : ℂ)‖ ≤
      49 * (Real.log (5 / 4))⁻¹ * (6 / 7 : ℝ) ^ M := by
  have hj : 1 ≤ Nat.log 2 n := Nat.log_pos (by decide) hn
  have h := cauchyApprox_invLog_error hM hj (mantissa_interval (by omega : 0 < n))
  rw [normalized_invLog (by omega : 0 < n)] at h
  exact h

theorem approximatePhase_error {M d x : ℕ} (hM : 0 < M) (hd : 0 < d) (hx : x < d) :
    ‖approximatePhase M d x - Ramanujan.phase d x‖ ≤
      49 * Real.exp (7 * Real.pi / 4) * (6 / 7 : ℝ) ^ M := by
  have h := cauchyApprox_phase_error hM (shifted_ratio_interval hd hx)
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_natCast, shiftedPhase_ratio] at h
  simpa only [approximatePhase, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast] using h

def analyticPrimeSum (M N : ℕ) : ℂ :=
  phaseSum N (fun n d x y => approximateLog M (n / d) * approximateInvLog M n *
    approximatePhase M n x * approximatePhase M d y)

/-- Actual finite Cauchy quadratures recover the exact integer for every N.
The only accuracy premises are three scalar inequalities in M and b. -/
theorem analyticPrimeSum_round {N b M : ℕ} (hN : N ≤ 2 ^ b) (hM : 0 < M)
    (hlog : 49 * ((b : ℝ) + 6) * (6 / 7 : ℝ) ^ M ≤ componentTolerance b)
    (hinv : 49 * (Real.log (5 / 4))⁻¹ * (6 / 7 : ℝ) ^ M ≤ componentTolerance b)
    (hphase : 49 * Real.exp (7 * Real.pi / 4) * (6 / 7 : ℝ) ^ M ≤ componentTolerance b) :
    ⌊(analyticPrimeSum M N).re + 1 / 2⌋ = (primeSum N : ℤ) := by
  apply primeSum_round_of_components N b hN
    (fun n d => approximateLog M (n / d)) (approximateInvLog M) (approximatePhase M)
  · intro n hn d hd
    have hnd : n / d ≤ 2 ^ b :=
      (Nat.div_le_self n d).trans ((mem_Icc.mp hn).2.trans hN)
    exact (approximateLog_error hM hnd).trans hlog
  · intro n hn
    exact (approximateInvLog_error hM (mem_Icc.mp hn).1).trans hinv
  · intro d hd x hx
    have hdp : 0 < d := (mem_Icc.mp hd).1
    have hxd : x < d := mem_range.mp (mem_filter.mp hx).1
    exact (approximatePhase_error hM hdp hxd).trans hphase

theorem approximateLog_accuracy {b n : ℕ} (hn : n ≤ 2 ^ b) :
    ‖approximateLog (primeNodes b) n - (Real.log n : ℂ)‖ ≤ componentTolerance b :=
  (approximateLog_error (primeNodes_pos b) hn).trans
    (coefficient_accuracy b ((b : ℝ) + 6) (by positivity) (log_coefficient_bound b))

theorem approximateInvLog_accuracy (b : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    ‖approximateInvLog (primeNodes b) n - (1 : ℂ) / (Real.log n : ℂ)‖ ≤
      componentTolerance b := by
  have h := invLog_approx_accuracy b (Nat.log 2 n) (Nat.log_pos (by decide) hn)
    (mantissa_interval (by omega : 0 < n))
  rw [normalized_invLog (by omega : 0 < n)] at h
  exact h

theorem approximatePhase_accuracy (b : ℕ) {d x : ℕ} (hd : 0 < d) (hx : x < d) :
    ‖approximatePhase (primeNodes b) d x - Ramanujan.phase d x‖ ≤ componentTolerance b := by
  have h := phase_approx_accuracy b (shifted_ratio_interval hd hx)
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_natCast, shiftedPhase_ratio] at h
  simpa only [approximatePhase, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast] using h

/-- No error hypotheses remain: the explicit linear node count is sufficient. -/
theorem analyticPrimeSum_primeNodes_round {N b : ℕ} (hN : N ≤ 2 ^ b) :
    ⌊(analyticPrimeSum (primeNodes b) N).re + 1 / 2⌋ = (primeSum N : ℤ) := by
  apply primeSum_round_of_components N b hN
    (fun n d => approximateLog (primeNodes b) (n / d))
    (approximateInvLog (primeNodes b)) (approximatePhase (primeNodes b))
  · intro n hn d hd
    exact approximateLog_accuracy ((Nat.div_le_self n d).trans ((mem_Icc.mp hn).2.trans hN))
  · intro n hn
    exact approximateInvLog_accuracy b (mem_Icc.mp hn).1
  · intro d hd x hx
    exact approximatePhase_accuracy b (mem_Icc.mp hd).1 (mem_range.mp (mem_filter.mp hx).1)

/-- The actual analytic quadrature formula gives the exact prime sum for every
natural input. No complexity or numerical-evaluator claim is part of this theorem. -/
theorem analyticPrimeSum_all_inputs (N : ℕ) :
    ⌊(analyticPrimeSum (primeNodes (Nat.log 2 N + 1)) N).re + 1 / 2⌋ =
      (primeSum N : ℤ) :=
  analyticPrimeSum_primeNodes_round (Nat.lt_pow_succ_log_self (by decide) N).le

end PrimeAlgorithm.CauchyPrimeSum
