import PrimeAlgorithm.CertifiedCauchy

/-! Exact prime summation from arbitrary certified integer coefficient tables.
The mathematical certificate is separate from the data and evaluator. -/

noncomputable section
namespace PrimeAlgorithm.CertifiedPrimeSum

open Finset PrimeAlgorithm.Cauchy PrimeAlgorithm.CauchyPrimeSum
  PrimeAlgorithm.CertifiedCauchy PrimeAlgorithm.DoubleRamanujan

structure PrimeData where
  pole : ℕ → GaussianIntPair
  logResidue : ℕ → ℕ → GaussianIntPair
  invLogResidue : ℕ → ℕ → GaussianIntPair
  phaseResidue : ℕ → GaussianIntPair

def logData (D : PrimeData) (j : ℕ) : Data := ⟨D.pole, D.logResidue j⟩
def invLogData (D : PrimeData) (j : ℕ) : Data := ⟨D.pole, D.invLogResidue j⟩
def phaseData (D : PrimeData) : Data := ⟨D.pole, D.phaseResidue⟩

structure Certified (b : ℕ) (D : PrimeData) : Prop where
  log : ∀ j, j ≤ b →
    Accurate (coefficientBits b) (nodeCount b) (logAmplitude j) (logData D j)
  invLog : ∀ j, 1 ≤ j → j ≤ b →
    Accurate (coefficientBits b) (nodeCount b) (invLogAmplitude j) (invLogData D j)
  phase : Accurate (coefficientBits b) (nodeCount b) shiftedPhase (phaseData D)

def approximateLog (b : ℕ) (D : PrimeData) (n : ℕ) : ℂ :=
  if n < 2 then 0 else primeEvaluate b (logData D (Nat.log 2 n)) (mantissa n)

def approximateInvLog (b : ℕ) (D : PrimeData) (n : ℕ) : ℂ :=
  primeEvaluate b (invLogData D (Nat.log 2 n)) (mantissa n)

def approximatePhase (b : ℕ) (D : PrimeData) (d x : ℕ) : ℂ :=
  primeEvaluate b (phaseData D) ((1 + (x : ℝ) / d : ℝ) : ℂ)

theorem log_accuracy {b : ℕ} {D : PrimeData} (hD : Certified b D)
    {n : ℕ} (hn : n ≤ 2 ^ b) :
    ‖approximateLog b D n - (Real.log n : ℂ)‖ ≤ componentTolerance b := by
  by_cases hs : n < 2
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;>
      simpa [approximateLog] using componentTolerance_nonneg b
  · have hnp : 0 < n := by omega
    have hj : Nat.log 2 n ≤ b := by
      simpa only [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hn
    have hbound : ∀ k ∈ range (nodeCount b),
        ‖logAmplitude (Nat.log 2 n) (sampleNode (nodeCount b) k)‖ ≤ (b : ℝ) + 2195 := by
      intro k _hk
      have hz : ‖sampleNode (nodeCount b) k - center‖ ≤ (7 / 8 : ℝ) := by
        rw [sampleNode_distance]
        norm_num
      have hjr : (Nat.log 2 n : ℝ) ≤ b := by exact_mod_cast hj
      exact (logAmplitude_norm_le _ hz).trans (by linarith)
    have h := primeEvaluate_accuracy b (hD.log _ hj) hbound (mantissa_interval hnp)
      (log_approx_accuracy ((b + 1) + 1) _ (by omega) (mantissa_interval hnp))
    rw [normalized_log hnp] at h
    simpa only [approximateLog, if_neg hs] using h

theorem invLog_accuracy {b : ℕ} {D : PrimeData} (hD : Certified b D)
    {n : ℕ} (hn : 2 ≤ n) (hnb : n ≤ 2 ^ b) :
    ‖approximateInvLog b D n - (1 : ℂ) / (Real.log n : ℂ)‖ ≤ componentTolerance b := by
  have hj : Nat.log 2 n ≤ b := by
    simpa only [Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hnb
  have hj1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by decide) hn
  have hbound : ∀ k ∈ range (nodeCount b),
      ‖invLogAmplitude (Nat.log 2 n) (sampleNode (nodeCount b) k)‖ ≤ (b : ℝ) + 2195 := by
    intro k _hk
    have hz : ‖sampleNode (nodeCount b) k - center‖ ≤ (7 / 8 : ℝ) := by
      rw [sampleNode_distance]
      norm_num
    have hb : (0 : ℝ) ≤ b := by positivity
    exact (invLogAmplitude_norm_le hj1 hz).trans (inverse_log_bound.trans (by linarith))
  have hy := mantissa_interval (by omega : 0 < n)
  have h := primeEvaluate_accuracy b (hD.invLog _ hj1 hj) hbound hy
    (invLog_approx_accuracy ((b + 1) + 1) _ hj1 hy)
  rw [normalized_invLog (by omega : 0 < n)] at h
  exact h

theorem phase_accuracy {b : ℕ} {D : PrimeData} (hD : Certified b D)
    {d x : ℕ} (hd : 0 < d) (hx : x < d) :
    ‖approximatePhase b D d x - Ramanujan.phase d x‖ ≤ componentTolerance b := by
  have hbound : ∀ k ∈ range (nodeCount b),
      ‖shiftedPhase (sampleNode (nodeCount b) k)‖ ≤ (b : ℝ) + 2195 := by
    intro k _hk
    have hz : ‖sampleNode (nodeCount b) k - center‖ ≤ (7 / 8 : ℝ) := by
      rw [sampleNode_distance]
      norm_num
    have hb : (0 : ℝ) ≤ b := by positivity
    exact (shiftedPhase_bound hz).trans (phase_exp_bound.trans (by linarith))
  have hy := shifted_ratio_interval hd hx
  have h := primeEvaluate_accuracy b hD.phase hbound hy
    (phase_approx_accuracy ((b + 1) + 1) hy)
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_natCast, shiftedPhase_ratio] at h
  simpa only [approximatePhase, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast] using h

def approximatePrimeSum (b : ℕ) (D : PrimeData) (N : ℕ) : ℂ :=
  phaseSum N (fun n d x y => approximateLog b D (n / d) * approximateInvLog b D n *
    approximatePhase b D n x * approximatePhase b D d y)

theorem primeSum_round {N b : ℕ} {D : PrimeData}
    (hN : N ≤ 2 ^ b) (hD : Certified b D) :
    ⌊(approximatePrimeSum b D N).re + 1 / 2⌋ = (primeSum N : ℤ) := by
  apply primeSum_round_of_components N b hN
    (fun n d => approximateLog b D (n / d)) (approximateInvLog b D) (approximatePhase b D)
  · intro n hn d _hd
    exact log_accuracy hD ((Nat.div_le_self n d).trans ((mem_Icc.mp hn).2.trans hN))
  · intro n hn
    exact invLog_accuracy hD (mem_Icc.mp hn).1 ((mem_Icc.mp hn).2.trans hN)
  · intro d hd x hx
    exact phase_accuracy hD (mem_Icc.mp hd).1 (mem_range.mp (mem_filter.mp hx).1)

/-- Any certified data table gives the exact answer, independently of the
algorithm or rounding convention used to generate its integer coordinates. -/
theorem primeSum_all_inputs (N : ℕ) (D : PrimeData)
    (hD : Certified (Nat.log 2 N + 1) D) :
    ⌊(approximatePrimeSum (Nat.log 2 N + 1) D N).re + 1 / 2⌋ = (primeSum N : ℤ) :=
  primeSum_round (Nat.lt_pow_succ_log_self (by decide) N).le hD

end PrimeAlgorithm.CertifiedPrimeSum
