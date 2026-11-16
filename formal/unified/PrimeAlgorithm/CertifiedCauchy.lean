import PrimeAlgorithm.FixedCauchyPrimeSum

/-! Cauchy evaluation from arbitrary certified dyadic integer data.
The evaluator reads only integer coordinates. Its certificate concerns their
distance from the analytic poles and residues, and does not prescribe an exact
floor or any other rounding convention for transcendental constants. -/

noncomputable section
namespace PrimeAlgorithm.CertifiedCauchy

open Finset PrimeAlgorithm.Cauchy PrimeAlgorithm.DoubleRamanujan
  PrimeAlgorithm.SignedQuantization

abbrev GaussianIntPair := ℤ × ℤ

def value (p : ℕ) (z : GaussianIntPair) : ℂ :=
  ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) / (2 : ℂ) ^ p

structure Data where
  pole : ℕ → GaussianIntPair
  residue : ℕ → GaussianIntPair

/-- Only the first M integer pairs are read. A computable generator may choose
any of the many pairs satisfying this certificate. -/
structure Accurate (p M : ℕ) (f : ℂ → ℂ) (D : Data) : Prop where
  pole_error : ∀ j ∈ range M,
    ‖value p (D.pole j) - sampleNode M j‖ ≤ 2 / (2 : ℝ) ^ p
  residue_error : ∀ j ∈ range M,
    ‖value p (D.residue j) - sampleResidue M j f‖ ≤ 2 / (2 : ℝ) ^ p

def exactValue (p M : ℕ) (D : Data) (y : ℂ) : ℂ :=
  (∑ j ∈ range M, value p (D.residue j) / (value p (D.pole j) - y)) / M

def evaluate (p t M : ℕ) (D : Data) (y : ℂ) : ℂ :=
  (∑ j ∈ range M, value p (D.residue j) *
    truncateComplex t (1 / (value p (D.pole j) - y))) / M

theorem exactValue_error {p M : ℕ} (hM : 0 < M)
    (hp : 2 / (2 : ℝ) ^ p ≤ 1 / 8) {f : ℂ → ℂ} {D : Data}
    (hD : Accurate p M f D) {H : ℝ} (hH : 0 ≤ H)
    (hf : ∀ j ∈ range M, ‖f (sampleNode M j)‖ ≤ H)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖exactValue p M D y - cauchyApprox M f y‖ ≤
      (8 + 32 * H) * (2 / (2 : ℝ) ^ p) := by
  rw [cauchyApprox_residues]
  apply average_error M hM
  intro j hj
  have hz := hD.pole_error j hj
  have hsep : (1 / 8 : ℝ) ≤ ‖value p (D.pole j) - y‖ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (sampleNode M j)
      (value p (D.pole j)) (y : ℂ)
    rw [norm_sub_rev (sampleNode M j) (value p (D.pole j))] at ht
    have hs := sampleNode_separation M j hy
    linarith
  apply quotient_perturbation _ _ _ _ H (2 / (2 : ℝ) ^ p) hH (by positivity)
  · rw [sampleResidue, norm_mul, sampleNode_distance]
    nlinarith [hf j hj, norm_nonneg (f (sampleNode M j))]
  · exact hD.residue_error j hj
  · simpa only [sub_sub_sub_cancel_right] using hz
  · exact sampleNode_separation M j hy
  · exact hsep

theorem evaluate_exactValue_error {p t M : ℕ} (hM : 0 < M)
    (D : Data) (y : ℂ) {H : ℝ} (hH : 0 ≤ H)
    (hf : ∀ j ∈ range M, ‖value p (D.residue j)‖ ≤ H) :
    ‖evaluate p t M D y - exactValue p M D y‖ ≤ H * (2 / (2 : ℝ) ^ t) := by
  apply average_error M hM
  intro j hj
  rw [show value p (D.residue j) / (value p (D.pole j) - y) =
    value p (D.residue j) * (1 / (value p (D.pole j) - y)) by ring,
    ← mul_sub, norm_mul]
  exact mul_le_mul (hf j hj) (truncateComplex_error t _) (norm_nonneg _) hH

def coefficientBits (b : ℕ) : ℕ := dyadicBits (b + 1)
def reciprocalBits (b : ℕ) : ℕ := dyadicBits b
def nodeCount (b : ℕ) : ℕ := primeNodes ((b + 1) + 1)

def primeEvaluate (b : ℕ) (D : Data) (y : ℂ) : ℂ :=
  evaluate (coefficientBits b) (reciprocalBits b) (nodeCount b) D y

theorem residue_bound {b : ℕ} {f : ℂ → ℂ} {D : Data}
    (hD : Accurate (coefficientBits b) (nodeCount b) f D)
    (hf : ∀ j ∈ range (nodeCount b), ‖f (sampleNode (nodeCount b) j)‖ ≤
      (b : ℝ) + 2195) {j : ℕ} (hj : j ∈ range (nodeCount b)) :
    ‖value (coefficientBits b) (D.residue j)‖ ≤ (b : ℝ) + 2196 := by
  have hq := hD.residue_error j hj
  have hs := dyadicBits_small (b + 1)
  have ht := norm_le_norm_sub_add
    (value (coefficientBits b) (D.residue j)) (sampleResidue (nodeCount b) j f)
  rw [sampleResidue, norm_mul, sampleNode_distance] at ht
  have hb : (0 : ℝ) ≤ b := by positivity
  dsimp only [coefficientBits, sampleResidue] at hq ht ⊢
  nlinarith [hf j hj]

/-- The explicit precisions cover coefficient perturbation, reciprocal
truncation and analytic quadrature simultaneously. -/
theorem primeEvaluate_accuracy (b : ℕ) {f : ℂ → ℂ} {D : Data}
    (hD : Accurate (coefficientBits b) (nodeCount b) f D)
    (hf : ∀ j ∈ range (nodeCount b), ‖f (sampleNode (nodeCount b) j)‖ ≤
      (b : ℝ) + 2195)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2)
    (he : ‖cauchyApprox (nodeCount b) f y - f y‖ ≤ componentTolerance ((b + 1) + 1)) :
    ‖primeEvaluate b D y - f y‖ ≤ componentTolerance b := by
  have hM : 0 < nodeCount b := primeNodes_pos _
  have hq := exactValue_error hM (dyadicBits_small (b + 1)) hD
    (by positivity : 0 ≤ (b : ℝ) + 2195) hf hy
  have hqb : ‖exactValue (coefficientBits b) (nodeCount b) D y -
      cauchyApprox (nodeCount b) f y‖ ≤ componentTolerance (b + 1) / 2 := by
    apply hq.trans
    have hshift : ((b + 1 : ℕ) : ℝ) + 2194 = (b : ℝ) + 2195 := by
      push_cast
      ring
    simpa only [coefficientBits, hshift] using
      dyadic_error_budget (b + 1)
  have htr := evaluate_exactValue_error (t := reciprocalBits b) hM D (y : ℂ)
    (by positivity : 0 ≤ (b : ℝ) + 2196) (fun j hj => residue_bound hD hf hj)
  have htrb : ‖primeEvaluate b D y -
      exactValue (coefficientBits b) (nodeCount b) D y‖ ≤ componentTolerance b / 2 := by
    apply htr.trans
    exact FixedCauchyPrimeSum.fixedBits_budget b
  have ht₁ := norm_sub_le_norm_sub_add_norm_sub
    (exactValue (coefficientBits b) (nodeCount b) D y)
    (cauchyApprox (nodeCount b) f y) (f y)
  have ht₂ := norm_sub_le_norm_sub_add_norm_sub (primeEvaluate b D y)
    (exactValue (coefficientBits b) (nodeCount b) D y) (f y)
  linarith [componentTolerance_step b, componentTolerance_step (b + 1)]

end PrimeAlgorithm.CertifiedCauchy
