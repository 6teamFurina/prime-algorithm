import PrimeAlgorithm.DyadicPrimeSum
import PrimeAlgorithm.SignedQuantization

/-! Each reciprocal term is rounded to an actual dyadic grid before averaging.
The resulting finite formula recovers primeSum for every natural input.
This module proves numerical correctness; coefficient generation and machine
running time are distinct assertions. -/

noncomputable section
namespace PrimeAlgorithm.FixedCauchyPrimeSum

open Finset PrimeAlgorithm.Cauchy PrimeAlgorithm.CauchyPrimeSum
  PrimeAlgorithm.DyadicPrimeSum PrimeAlgorithm.DoubleRamanujan
  PrimeAlgorithm.PhaseApproximation PrimeAlgorithm.SignedQuantization

def fixedCauchy (p t M : ℕ) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  (∑ j ∈ range M, quantizeComplex p (sampleResidue M j f) *
    truncateComplex t (1/(quantizeComplex p (sampleNode M j)-y))) / (M : ℂ)

/-- Quantizing each reciprocal term does not accumulate an extra factor M. -/
theorem fixedCauchy_error {p t M : ℕ} (hM : 0<M) (f : ℂ → ℂ) (y : ℂ)
    {H : ℝ} (hH : 0≤H)
    (hf : ∀j∈range M, ‖quantizeComplex p (sampleResidue M j f)‖≤H) :
    ‖fixedCauchy p t M f y-dyadicCauchy p M f y‖ ≤ H*(2/(2:ℝ)^t) := by
  apply average_error M hM
  intro j hj
  rw [show quantizeComplex p (sampleResidue M j f) /
      (quantizeComplex p (sampleNode M j)-y) =
    quantizeComplex p (sampleResidue M j f) *
      (1/(quantizeComplex p (sampleNode M j)-y)) by ring,
    ←mul_sub,norm_mul]
  exact mul_le_mul (hf j hj) (truncateComplex_error t _)
    (norm_nonneg _) hH

def fixedBits (b : ℕ) : ℕ := dyadicBits b

theorem fixedBits_budget (b : ℕ) :
    ((b:ℝ)+2196)*(2/(2:ℝ)^fixedBits b) ≤ componentTolerance b/2 := by
  apply le_trans _ (dyadic_error_budget b)
  unfold fixedBits
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hb : (0:ℝ)≤b := by positivity
  linarith

theorem quantizedResidue_bound (b M j : ℕ) (f : ℂ → ℂ)
    (hf : ‖f (sampleNode M j)‖≤(b:ℝ)+2195) :
    ‖quantizeComplex (dyadicBits (b+1)) (sampleResidue M j f)‖≤(b:ℝ)+2196 := by
  have hq := quantizeComplex_error (dyadicBits (b+1)) (sampleResidue M j f)
  have hs := dyadicBits_small (b+1)
  have ht := norm_le_norm_sub_add
    (quantizeComplex (dyadicBits (b+1)) (sampleResidue M j f)) (sampleResidue M j f)
  have hr : ‖sampleResidue M j f‖≤((b:ℝ)+2195)*(3/4) := by
    rw [sampleResidue,norm_mul,sampleNode_distance]
    exact mul_le_mul_of_nonneg_right hf (by norm_num)
  have hb : (0:ℝ)≤b := by positivity
  nlinarith

theorem fixedCauchy_dyadic_error (b : ℕ) (f : ℂ → ℂ) (y : ℂ)
    (hf : ∀j∈range (primeNodes ((b+1)+1)),
      ‖f (sampleNode (primeNodes ((b+1)+1)) j)‖≤(b:ℝ)+2195) :
    ‖fixedCauchy (dyadicBits (b+1)) (fixedBits b) (primeNodes ((b+1)+1)) f y-
      dyadicCauchy (dyadicBits (b+1)) (primeNodes ((b+1)+1)) f y‖≤
      componentTolerance b/2 := by
  apply le_trans (fixedCauchy_error (primeNodes_pos ((b+1)+1)) f y
    (by positivity : 0≤(b:ℝ)+2196) ?_) (fixedBits_budget b)
  intro j hj
  exact quantizedResidue_bound b _ j f (hf j hj)

def fixedLog (b n : ℕ) : ℂ :=
  if n<2 then 0 else
    fixedCauchy (dyadicBits (b+1)) (fixedBits b) (primeNodes ((b+1)+1))
      (logAmplitude (Nat.log 2 n)) (mantissa n)

def fixedInvLog (b n : ℕ) : ℂ :=
  fixedCauchy (dyadicBits (b+1)) (fixedBits b) (primeNodes ((b+1)+1))
    (invLogAmplitude (Nat.log 2 n)) (mantissa n)

def fixedPhase (b d x : ℕ) : ℂ :=
  fixedCauchy (dyadicBits (b+1)) (fixedBits b) (primeNodes ((b+1)+1))
    shiftedPhase ((1+(x:ℝ)/d:ℝ):ℂ)

theorem fixedLog_dyadic_error {b n : ℕ} (hn' : n≤2^b) :
    ‖fixedLog b n-dyadicLog (b+1) n‖ ≤ componentTolerance b/2 := by
  by_cases hn : n<2
  · simpa [fixedLog,dyadicLog,hn] using div_nonneg (componentTolerance_nonneg b) (by norm_num : (0:ℝ)≤2)
  · simp only [fixedLog,dyadicLog,if_neg hn]
    apply fixedCauchy_dyadic_error
    intro j _hj
    have hb : Nat.log 2 n≤b := by
      simpa only [Nat.log_pow (by decide : 1<2)] using Nat.log_mono_right (b:=2) hn'
    have hbr : (Nat.log 2 n:ℝ)≤b := by exact_mod_cast hb
    have hs : ‖sampleNode (primeNodes ((b+1)+1)) j-center‖≤(7/8:ℝ) := by
      rw [sampleNode_distance]
      norm_num
    exact (logAmplitude_norm_le (Nat.log 2 n) hs).trans (by linarith)

theorem fixedInvLog_dyadic_error (b : ℕ) {n : ℕ} (hn : 2≤n) :
    ‖fixedInvLog b n-dyadicInvLog (b+1) n‖ ≤ componentTolerance b/2 := by
  apply fixedCauchy_dyadic_error
  intro j _hj
  have hs : ‖sampleNode (primeNodes ((b+1)+1)) j-center‖≤(7/8:ℝ) := by
    rw [sampleNode_distance]
    norm_num
  have hb : (0:ℝ)≤b := by positivity
  exact (invLogAmplitude_norm_le (Nat.log_pos (by decide) hn) hs).trans
    (inverse_log_bound.trans (by linarith))

theorem fixedPhase_dyadic_error (b d x : ℕ) :
    ‖fixedPhase b d x-dyadicPhase (b+1) d x‖ ≤ componentTolerance b/2 := by
  apply fixedCauchy_dyadic_error
  intro j _hj
  have hs : ‖sampleNode (primeNodes ((b+1)+1)) j-center‖≤(7/8:ℝ) := by
    rw [sampleNode_distance]
    norm_num
  have hb : (0:ℝ)≤b := by positivity
  exact (shiftedPhase_bound hs).trans (phase_exp_bound.trans (by linarith))

theorem fixedLog_accuracy {b n : ℕ} (hn : n≤2^b) :
    ‖fixedLog b n-(Real.log n:ℂ)‖ ≤ componentTolerance b := by
  have hn' : n≤2^(b+1) := hn.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (fixedLog b n) (dyadicLog (b+1) n) (Real.log n:ℂ)
  linarith [fixedLog_dyadic_error hn,dyadicLog_accuracy hn',componentTolerance_step b]

theorem fixedInvLog_accuracy (b : ℕ) {n : ℕ} (hn : 2≤n) :
    ‖fixedInvLog b n-(1:ℂ)/(Real.log n:ℂ)‖ ≤ componentTolerance b := by
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (fixedInvLog b n) (dyadicInvLog (b+1) n) ((1:ℂ)/(Real.log n:ℂ))
  linarith [fixedInvLog_dyadic_error b hn,dyadicInvLog_accuracy (b+1) hn,
    componentTolerance_step b]

theorem fixedPhase_accuracy (b : ℕ) {d x : ℕ} (hd : 0<d) (hx : x<d) :
    ‖fixedPhase b d x-Ramanujan.phase d x‖ ≤ componentTolerance b := by
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (fixedPhase b d x) (dyadicPhase (b+1) d x) (Ramanujan.phase d x)
  linarith [fixedPhase_dyadic_error b d x,dyadicPhase_accuracy (b+1) hd hx,
    componentTolerance_step b]

def fixedPrimeSum (b N : ℕ) : ℂ :=
  phaseSum N (fun n d x y =>
    fixedLog b (n/d)*fixedInvLog b n*fixedPhase b n x*fixedPhase b d y)

/-- All reciprocal kernels are rounded before being multiplied and summed. -/
theorem fixedPrimeSum_round {N b : ℕ} (hN : N≤2^b) :
    ⌊(fixedPrimeSum b N).re+1/2⌋=(primeSum N:ℤ) := by
  apply primeSum_round_of_components N b hN
    (fun n d => fixedLog b (n/d)) (fixedInvLog b) (fixedPhase b)
  · intro n hn d _hd
    exact fixedLog_accuracy ((Nat.div_le_self n d).trans ((mem_Icc.mp hn).2.trans hN))
  · intro n hn
    exact fixedInvLog_accuracy b (mem_Icc.mp hn).1
  · intro d hd x hx
    exact fixedPhase_accuracy b (mem_Icc.mp hd).1 (mem_range.mp (mem_filter.mp hx).1)

/-- Exact rounding for every N with explicit logarithmic precision and node count. -/
theorem fixedPrimeSum_all_inputs (N : ℕ) :
    ⌊(fixedPrimeSum (Nat.log 2 N+1) N).re+1/2⌋=(primeSum N:ℤ) :=
  fixedPrimeSum_round (Nat.lt_pow_succ_log_self (by decide) N).le

end PrimeAlgorithm.FixedCauchyPrimeSum
