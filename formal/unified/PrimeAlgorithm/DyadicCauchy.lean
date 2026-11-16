import PrimeAlgorithm.CauchyPrimeSum
import PrimeAlgorithm.CauchyPerturbation

/-! Dyadic poles and residues for the actual Cauchy formula. These are
mathematical finite-precision data; efficient generation of their integer
numerators is a separate computational assertion. -/

noncomputable section
namespace PrimeAlgorithm.Cauchy
open Finset PrimeAlgorithm.PhaseApproximation

def sampleRoot (M j : ℕ) : ℂ := (Complex.exp (2 * Real.pi * Complex.I / M)) ^ j
def sampleNode (M j : ℕ) : ℂ := center + (3 / 4 : ℂ) * sampleRoot M j
def sampleResidue (M j : ℕ) (f : ℂ → ℂ) : ℂ :=
  f (sampleNode M j) * (sampleNode M j - center)

theorem sampleRoot_norm (M j : ℕ) : ‖sampleRoot M j‖ = 1 := by
  simp [sampleRoot, norm_pow, Complex.norm_exp, Complex.div_re]

theorem sampleNode_distance (M j : ℕ) : ‖sampleNode M j - center‖ = (3 / 4 : ℝ) := by
  simp [sampleNode, norm_mul, sampleRoot_norm]

theorem sampleNode_separation (M j : ℕ) {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    (1 / 4 : ℝ) ≤ ‖sampleNode M j - y‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub (sampleNode M j) (y : ℂ) center
  rw [sampleNode_distance] at h
  have := interval_distance hy
  linarith

theorem cauchyApprox_residues (M : ℕ) (f : ℂ → ℂ) (y : ℂ) :
    cauchyApprox M f y =
      (∑ j ∈ range M, sampleResidue M j f / (sampleNode M j - y)) / (M : ℂ) := by
  unfold cauchyApprox quadrature
  congr 1
  apply sum_congr rfl
  intro j _hj
  rw [← mul_div_assoc]
  change f (sampleNode M j) * sampleRoot M j /
    (sampleRoot M j - (y - center) / (3 / 4)) = _
  have hd : sampleNode M j - y =
      (3 / 4 : ℂ) * (sampleRoot M j - (y - center) / (3 / 4)) := by
    unfold sampleNode
    ring
  rw [sampleResidue, hd]
  simp only [sampleNode, add_sub_cancel_left]
  rw [show f (center + (3 / 4 : ℂ) * sampleRoot M j) * ((3 / 4) * sampleRoot M j) =
    (3 / 4) * (f (center + (3 / 4 : ℂ) * sampleRoot M j) * sampleRoot M j) by ring]
  rw [mul_div_mul_left _ _ (by norm_num : (3 / 4 : ℂ) ≠ 0)]

def dyadicCauchy (p M : ℕ) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  (∑ j ∈ range M, quantizeComplex p (sampleResidue M j f) /
    (quantizeComplex p (sampleNode M j) - y)) / (M : ℂ)

theorem dyadicCauchy_error {M p : ℕ} (hM : 0 < M)
    (hp : 2 / (2 : ℝ) ^ p ≤ 1 / 8) {f : ℂ → ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hf : ∀ j ∈ range M, ‖f (sampleNode M j)‖ ≤ H)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖dyadicCauchy p M f y - cauchyApprox M f y‖ ≤
      (8 + 32 * H) * (2 / (2 : ℝ) ^ p) := by
  rw [cauchyApprox_residues]
  apply average_error M hM
  intro j hj
  have hz := quantizeComplex_error p (sampleNode M j)
  have hsep : (1 / 8 : ℝ) ≤ ‖quantizeComplex p (sampleNode M j) - y‖ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (sampleNode M j)
      (quantizeComplex p (sampleNode M j)) (y : ℂ)
    rw [norm_sub_rev (sampleNode M j) (quantizeComplex p (sampleNode M j))] at ht
    have hs := sampleNode_separation M j hy
    linarith
  apply quotient_perturbation _ _ _ _ H (2 / (2 : ℝ) ^ p) hH (by positivity)
  · rw [sampleResidue, norm_mul, sampleNode_distance]
    nlinarith [hf j hj, norm_nonneg (f (sampleNode M j))]
  · exact quantizeComplex_error p _
  · simpa only [sub_sub_sub_cancel_right] using hz
  · exact sampleNode_separation M j hy
  · exact hsep

def dyadicBits (b : ℕ) : ℕ := 7 * b + 25

theorem dyadicBits_small (b : ℕ) : 2 / (2 : ℝ) ^ dyadicBits b ≤ 1 / 8 := by
  have h : (16 : ℝ) ≤ (2 : ℝ) ^ dyadicBits b := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by unfold dyadicBits; omega)
  apply (div_le_iff₀ (by positivity)).2
  linarith

theorem dyadic_error_budget (b : ℕ) :
    (8 + 32 * ((b : ℝ) + 2194)) * (2 / (2 : ℝ) ^ dyadicBits b) ≤
      DoubleRamanujan.componentTolerance b / 2 := by
  have hb : (b : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast (Nat.lt_two_pow_self (n := b)).le
  have ht : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  have hc : (8 + 32 * ((b : ℝ) + 2194)) * 2 ≤ (2 : ℝ) ^ (b + 18) := by
    rw [pow_add]
    norm_num
    linarith
  rw [DoubleRamanujan.componentTolerance_dyadic, dyadicBits]
  calc
    _ = ((8 + 32 * ((b : ℝ) + 2194)) * 2) / (2 : ℝ) ^ (7 * b + 25) := by ring
    _ ≤ (2 : ℝ) ^ (b + 18) / (2 : ℝ) ^ (7 * b + 25) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = 1 / (2 : ℝ) ^ (6 * b + 6) / 2 := by
      rw [show 7 * b + 25 = (b + 18) + ((6 * b + 6) + 1) by omega]
      simp only [pow_add, pow_one]
      field_simp

theorem componentTolerance_step (b : ℕ) :
    DoubleRamanujan.componentTolerance (b + 1) ≤
      DoubleRamanujan.componentTolerance b / 2 := by
  rw [DoubleRamanujan.componentTolerance_dyadic, DoubleRamanujan.componentTolerance_dyadic,
    show 6 * (b + 1) + 6 = (6 * b + 6) + 6 by omega, pow_add]
  have ht : (0 : ℝ) < 2 ^ (6 * b + 6) := by positivity
  apply (div_le_iff₀ (by positivity)).2
  field_simp
  norm_num

theorem sampleNode_mem (M j : ℕ) :
    sampleNode M j ∈ Metric.closedBall center (7 / 8) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sampleNode_distance]
  norm_num

theorem dyadicCauchy_accuracy (b : ℕ) {f : ℂ → ℂ} {y : ℝ}
    (hy : y ∈ Set.Icc 1 2)
    (hf : ∀ j ∈ range (primeNodes (b + 1)), ‖f (sampleNode (primeNodes (b + 1)) j)‖ ≤
      (b : ℝ) + 2194)
    (he : ‖cauchyApprox (primeNodes (b + 1)) f y - f y‖ ≤
      DoubleRamanujan.componentTolerance (b + 1)) :
    ‖dyadicCauchy (dyadicBits b) (primeNodes (b + 1)) f y - f y‖ ≤
      DoubleRamanujan.componentTolerance b := by
  have hq := dyadicCauchy_error (primeNodes_pos (b + 1)) (dyadicBits_small b)
    (by positivity : 0 ≤ (b : ℝ) + 2194) hf hy
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (dyadicCauchy (dyadicBits b) (primeNodes (b + 1)) f y)
    (cauchyApprox (primeNodes (b + 1)) f y) (f y)
  linarith [dyadic_error_budget b, componentTolerance_step b]

end PrimeAlgorithm.Cauchy
