import PrimeAlgorithm.DyadicCauchy

/-! Dyadic poles and residues give an exact prime-sum rounding formula for
every natural input. The divisions in this formula are exact rational
divisions; no assertion about an efficient coefficient generator is made. -/

noncomputable section
namespace PrimeAlgorithm.DyadicPrimeSum

open Finset PrimeAlgorithm.Cauchy PrimeAlgorithm.CauchyPrimeSum
  PrimeAlgorithm.DoubleRamanujan

theorem dyadic_logAmplitude_accuracy (b j : ℕ) (hj : j ≤ b)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖dyadicCauchy (dyadicBits b) (primeNodes (b + 1)) (logAmplitude j) y -
      logAmplitude j y‖ ≤ componentTolerance b := by
  apply dyadicCauchy_accuracy b hy
  · intro k _hk
    have hs : ‖sampleNode (primeNodes (b + 1)) k - center‖ ≤ (7 / 8 : ℝ) := by
      rw [sampleNode_distance]
      norm_num
    have hjr : (j : ℝ) ≤ b := by exact_mod_cast hj
    exact (logAmplitude_norm_le j hs).trans (by linarith)
  · exact log_approx_accuracy (b + 1) j (by omega) hy

theorem dyadic_invLogAmplitude_accuracy (b j : ℕ) (hj : 1 ≤ j)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖dyadicCauchy (dyadicBits b) (primeNodes (b + 1)) (invLogAmplitude j) y -
      invLogAmplitude j y‖ ≤ componentTolerance b := by
  apply dyadicCauchy_accuracy b hy
  · intro k _hk
    have hs : ‖sampleNode (primeNodes (b + 1)) k - center‖ ≤ (7 / 8 : ℝ) := by
      rw [sampleNode_distance]
      norm_num
    exact (invLogAmplitude_norm_le hj hs).trans
      (inverse_log_bound.trans (by
        have : (0 : ℝ) ≤ b := by positivity
        linarith))
  · exact invLog_approx_accuracy (b + 1) j hj hy

theorem dyadic_shiftedPhase_accuracy (b : ℕ) {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖dyadicCauchy (dyadicBits b) (primeNodes (b + 1)) shiftedPhase y -
      shiftedPhase y‖ ≤ componentTolerance b := by
  apply dyadicCauchy_accuracy b hy
  · intro k _hk
    have hs : ‖sampleNode (primeNodes (b + 1)) k - center‖ ≤ (7 / 8 : ℝ) := by
      rw [sampleNode_distance]
      norm_num
    exact (shiftedPhase_bound hs).trans
      (phase_exp_bound.trans (by
        have : (0 : ℝ) ≤ b := by positivity
        linarith))
  · exact phase_approx_accuracy (b + 1) hy

def dyadicLog (b n : ℕ) : ℂ :=
  if n < 2 then 0 else
    dyadicCauchy (dyadicBits b) (primeNodes (b + 1))
      (logAmplitude (Nat.log 2 n)) (mantissa n)

def dyadicInvLog (b n : ℕ) : ℂ :=
  dyadicCauchy (dyadicBits b) (primeNodes (b + 1))
    (invLogAmplitude (Nat.log 2 n)) (mantissa n)

def dyadicPhase (b d x : ℕ) : ℂ :=
  dyadicCauchy (dyadicBits b) (primeNodes (b + 1)) shiftedPhase
    ((1 + (x : ℝ) / d : ℝ) : ℂ)

theorem dyadicLog_accuracy {b n : ℕ} (hn : n ≤ 2 ^ b) :
    ‖dyadicLog b n - (Real.log n : ℂ)‖ ≤ componentTolerance b := by
  by_cases hs : n < 2
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;>
      simpa [dyadicLog] using componentTolerance_nonneg b
  · have hnp : 0 < n := by omega
    have hj : Nat.log 2 n ≤ b := by
      have h := Nat.log_mono_right (b := 2) hn
      simpa only [Nat.log_pow (by decide : 1 < 2)] using h
    have h := dyadic_logAmplitude_accuracy b (Nat.log 2 n) hj (mantissa_interval hnp)
    rw [normalized_log hnp] at h
    simpa only [dyadicLog, if_neg hs] using h

theorem dyadicInvLog_accuracy (b : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    ‖dyadicInvLog b n - (1 : ℂ) / (Real.log n : ℂ)‖ ≤ componentTolerance b := by
  have h := dyadic_invLogAmplitude_accuracy b (Nat.log 2 n)
    (Nat.log_pos (by decide) hn) (mantissa_interval (by omega : 0 < n))
  rw [normalized_invLog (by omega : 0 < n)] at h
  exact h

theorem dyadicPhase_accuracy (b : ℕ) {d x : ℕ} (hd : 0 < d) (hx : x < d) :
    ‖dyadicPhase b d x - Ramanujan.phase d x‖ ≤ componentTolerance b := by
  have h := dyadic_shiftedPhase_accuracy b (shifted_ratio_interval hd hx)
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_natCast, shiftedPhase_ratio] at h
  simpa only [dyadicPhase, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast] using h

def dyadicPrimeSum (b N : ℕ) : ℂ :=
  phaseSum N (fun n d x y =>
    dyadicLog b (n / d) * dyadicInvLog b n * dyadicPhase b n x * dyadicPhase b d y)

/-- All four dyadic component errors are proved for the actual formula. -/
theorem dyadicPrimeSum_round {N b : ℕ} (hN : N ≤ 2 ^ b) :
    ⌊(dyadicPrimeSum b N).re + 1 / 2⌋ = (primeSum N : ℤ) := by
  apply primeSum_round_of_components N b hN
    (fun n d => dyadicLog b (n / d)) (dyadicInvLog b) (dyadicPhase b)
  · intro n hn d _hd
    exact dyadicLog_accuracy ((Nat.div_le_self n d).trans ((mem_Icc.mp hn).2.trans hN))
  · intro n hn
    exact dyadicInvLog_accuracy b (mem_Icc.mp hn).1
  · intro d hd x hx
    exact dyadicPhase_accuracy b (mem_Icc.mp hd).1 (mem_range.mp (mem_filter.mp hx).1)

/-- An unconditional exact rounding identity for every natural input. -/
theorem dyadicPrimeSum_all_inputs (N : ℕ) :
    ⌊(dyadicPrimeSum (Nat.log 2 N + 1) N).re + 1 / 2⌋ = (primeSum N : ℤ) :=
  dyadicPrimeSum_round (Nat.lt_pow_succ_log_self (by decide) N).le

end PrimeAlgorithm.DyadicPrimeSum
