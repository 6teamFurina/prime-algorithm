import PrimeAlgorithm.CertifiedGenerator
import PrimeAlgorithm.CertifiedGeneratorBudget

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048

noncomputable section
open scoped QuadraticAlgebra
namespace PrimeAlgorithm.CertifiedGenerator

open Finset Cauchy CertifiedRawGaussian CertifiedRawTaylor CertifiedRawPi
  CertifiedNearest CertifiedGaussianRat CertifiedCauchy CertifiedPrimeSum
  CertifiedAnalyticStability

abbrev eval (z : Raw) : ℂ := embed (interpret z)

theorem eval_add {z w : Raw} (hz : Valid z) (hw : Valid w) :
    eval (add z w) = eval z + eval w := by simp only [eval, interpret_add hz hw, map_add]
theorem eval_mul {z w : Raw} (hz : Valid z) (hw : Valid w) :
    eval (mul z w) = eval z * eval w := by simp only [eval, interpret_mul hz hw, map_mul]
theorem eval_neg (z : Raw) : eval (neg z) = -eval z := by simp only [eval, interpret_neg, map_neg]
theorem eval_inv {z : Raw} (hz : Valid z) : eval (inv z) = (eval z)⁻¹ := by
  simp only [eval, interpret_inv hz, map_inv₀]
theorem eval_ofInt (n : ℤ) : eval (ofInt n) = n := by simp only [eval, interpret_ofInt, map_intCast]

theorem eval_formula (z : Raw) :
    eval z = ((z.1 : ℂ) + (z.2.1 : ℂ) * Complex.I) / z.2.2 := embed_interpret z
theorem eval_expTaylor (m : ℕ) {z : Raw} (hz : Valid z) :
    eval (polynomial false m z) = embed (expTaylor m (interpret z)) := exp_correct m hz
theorem eval_logTaylor (m : ℕ) {z : Raw} (hz : Valid z) :
    eval (polynomial true m z) = embed (logTaylor m (interpret z)) := log_correct m hz
theorem eval_pi (m : ℕ) : eval (pi m) = (CertifiedSeries.piRat m : ℂ) := pi_correct m

theorem rawExp_error (b : ℕ) {z : Raw} (hz : Valid z) (hn : ‖eval z‖ ≤ 16) :
    ‖eval (rawExp b z) - Complex.exp (eval z)‖ ≤
      (2 : ℝ) ^ 125 * (1 / 2 : ℝ) ^ order b := by
  rw [rawExp, eval_expTaylor _ hz]
  exact expTaylor_large_error _ _ hn

theorem rawLogTwo_correct (b : ℕ) :
    eval (rawLogTwo b) = embed (logTwo (logOrder b)) := by
  rw [rawLogTwo, eval_neg, eval_logTaylor _ (by norm_num [Valid]), logTwo, map_neg]
  have he : interpret (-1, 0, 2) = (-1 / 2 : QComplex) := by
    ext <;> norm_num [interpret, QuadraticAlgebra.re_div, QuadraticAlgebra.im_div, QuadraticAlgebra.norm_def, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  rw [he]

theorem rawLog_correct (b : ℕ) {z : Raw} (hz : Valid z) :
    eval (rawLog b z) = embed (logScaled (logOrder b) (interpret z)) := by
  rw [rawLog, eval_add (rawLogTwo_valid _)
    (polynomial_valid _ _ (valid_add (valid_mul hz (by norm_num [Valid])) (valid_ofInt _))),
    rawLogTwo_correct, eval_logTaylor _ (valid_add (valid_mul hz (by norm_num [Valid])) (valid_ofInt _)),
    logScaled, map_add]
  have he : interpret (1, 0, 2) = (1 / 2 : QComplex) := by
    ext <;> norm_num [interpret, QuadraticAlgebra.re_div, QuadraticAlgebra.im_div, QuadraticAlgebra.norm_def, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  have harg : interpret (add (mul z (1, 0, 2)) (ofInt (-1))) = interpret z / 2 - 1 := by
    rw [interpret_add (valid_mul hz (by norm_num [Valid])) (valid_ofInt _),
      interpret_mul hz (by norm_num [Valid]), interpret_ofInt, he]
    push_cast
    ring
  rw [harg]

theorem rawAngle_correct (b : ℕ) :
    eval (rawAngle b) = 2 * (CertifiedSeries.piRat (order b) : ℂ) * Complex.I := by
  rw [rawAngle, eval_mul (pi_valid _) (by norm_num [Valid]), eval_pi, eval_formula (0, 2, 1)]
  norm_num
  ring

theorem rawNode_correct (b j : ℕ) :
    eval (rawNode b j) = center + (3 / 4 : ℂ) *
      eval (rawExp b (mul (rawAngle b) (j, 0, nodeCount b))) := by
  rw [rawNode, eval_add (by norm_num [Valid])
    (valid_mul (by norm_num [Valid])
      (rawExp_valid _ (valid_mul (rawAngle_valid _) (show Valid (j, 0, nodeCount b) from primeNodes_pos _)))),
    eval_mul (by norm_num [Valid])
      (rawExp_valid _ (valid_mul (rawAngle_valid _) (show Valid (j, 0, nodeCount b) from primeNodes_pos _)))]
  rw [eval_formula (3, 0, 2), eval_formula (3, 0, 4)]
  norm_num [center]

theorem rawNodeArgument_correct (b j : ℕ) :
    eval (mul (rawAngle b) (j, 0, nodeCount b)) =
      eval (rawAngle b) * ((j : ℂ) / nodeCount b) := by
  rw [eval_mul (rawAngle_valid _) (show Valid (j, 0, nodeCount b) from primeNodes_pos _), eval_formula (j, 0, nodeCount b)]
  simp

theorem rawLogAmplitude_correct (b l j : ℕ) :
    eval (rawLogAmplitude b l j) =
      (l : ℂ) * eval (rawLogTwo b) + eval (rawLog b (rawNode b j)) := by
  rw [rawLogAmplitude, eval_add (valid_mul (valid_ofInt _) (rawLogTwo_valid _))
    (rawLog_valid _ (rawNode_valid _ _)), eval_mul (valid_ofInt _) (rawLogTwo_valid _), eval_ofInt]
  simp

theorem rawPhaseArgument_correct (b j : ℕ) :
    eval (mul (rawAngle b) (add (rawNode b j) (ofInt (-1)))) =
      eval (rawAngle b) * (eval (rawNode b j) - 1) := by
  rw [eval_mul (rawAngle_valid _) (valid_add (rawNode_valid _ _) (valid_ofInt _)),
    eval_add (rawNode_valid _ _) (valid_ofInt _), eval_ofInt]
  push_cast
  ring

theorem rawResidue_correct (b j : ℕ) {f : Raw} (hf : Valid f) :
    eval (rawResidue b j f) = eval f * (eval (rawNode b j) - center) := by
  rw [rawResidue, eval_mul hf (valid_add (rawNode_valid _ _) (by norm_num [Valid])),
    eval_add (rawNode_valid _ _) (by norm_num [Valid]), eval_formula (-3, 0, 2)]
  simp only [center]
  push_cast
  ring

theorem geometric_log_rate (k : ℕ) : (3 / 4 : ℝ) ^ (4 * k + 1) ≤ (1 / 2 : ℝ) ^ k := by
  rw [pow_add, pow_one, pow_mul]
  have h : ((3 / 4 : ℝ) ^ 4) ^ k ≤ (1 / 2 : ℝ) ^ k := by gcongr <;> norm_num
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]

theorem rawLogTwo_error (b : ℕ) :
    ‖eval (rawLogTwo b) - (Real.log 2 : ℂ)‖ ≤ 4 * (1 / 2 : ℝ) ^ order b := by
  rw [rawLogTwo_correct]
  exact (logTwo_error (4 * order b)).trans (by
    gcongr
    exact geometric_log_rate _)

theorem rawLog_error (b : ℕ) {z : Raw} (hz : Valid z)
    (hd : ‖eval z - center‖ ≤ (7 / 8 : ℝ)) :
    ‖eval (rawLog b z) - Complex.log (eval z)‖ ≤ 8 * (1 / 2 : ℝ) ^ order b := by
  have hn : ‖eval z / 2 - 1‖ ≤ (3 / 4 : ℝ) := by
    have he : eval z / 2 - 1 = (eval z - center) / 2 - 1 / 4 := by simp only [center]; push_cast; ring
    rw [he]
    have h := norm_sub_le ((eval z - center) / 2) (1 / 4 : ℂ)
    norm_num [norm_div] at h
    linarith
  have h0 : eval z ≠ 0 := by
    intro he
    have hl := disk_norm_lower hd
    norm_num [he] at hl
  rw [rawLog_correct _ hz]
  exact (logScaled_error (4 * order b) (interpret z) hn h0).trans (by
    gcongr
    exact geometric_log_rate _)

def trueAngle : ℂ := 2 * Real.pi * Complex.I

theorem trueAngle_norm : ‖trueAngle‖ ≤ (8 : ℝ) := by
  have hp := Real.pi_le_four
  norm_num [trueAngle, norm_mul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  linarith

theorem rawAngle_error (b : ℕ) : ‖eval (rawAngle b) - trueAngle‖ ≤ 32 * eta b := by
  have hp := CertifiedSeries.piRat_error (order b)
  have hrate : (1 / 4 : ℝ) ^ order b ≤ (1 / 2 : ℝ) ^ order b := by gcongr <;> norm_num
  have he : eval (rawAngle b) - trueAngle =
      2 * ((CertifiedSeries.piRat (order b) : ℂ) - (Real.pi : ℂ)) * Complex.I := by
    rw [rawAngle_correct, trueAngle]
    ring
  rw [he, norm_mul, norm_mul]
  have hc : ‖(CertifiedSeries.piRat (order b) : ℂ) - (Real.pi : ℂ)‖ =
      |(CertifiedSeries.piRat (order b) : ℝ) - Real.pi| := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hc]
  norm_num
  dsimp only [eta]
  linarith

theorem rawAngle_norm (b : ℕ) : ‖eval (rawAngle b)‖ ≤ (9 : ℝ) := by
  have ht := norm_le_norm_sub_add (eval (rawAngle b)) trueAngle
  linarith [rawAngle_error b, eta_thirtytwo_le_one b, trueAngle_norm]

theorem sample_ratio_norm {b j : ℕ} (hj : j < nodeCount b) :
    ‖(j : ℂ) / nodeCount b‖ ≤ (1 : ℝ) := by
  have hM : (0 : ℝ) < nodeCount b := by exact_mod_cast (primeNodes_pos ((b + 1) + 1))
  have hj' : (j : ℝ) ≤ nodeCount b := by exact_mod_cast hj.le
  simpa only [norm_div, Complex.norm_natCast] using (div_le_one hM).2 hj'

theorem sampleRoot_exp (b j : ℕ) :
    sampleRoot (nodeCount b) j = Complex.exp (trueAngle * ((j : ℂ) / nodeCount b)) := by
  simpa only [sampleRoot, trueAngle, Ramanujan.phase] using
    (Ramanujan.phase_eq_pow (nodeCount b) j).symm

theorem rawNodeArgument_error {b j : ℕ} (hj : j < nodeCount b) :
    ‖eval (mul (rawAngle b) (j, 0, nodeCount b)) -
      trueAngle * ((j : ℂ) / nodeCount b)‖ ≤ 32 * eta b := by
  rw [rawNodeArgument_correct, ← sub_mul, norm_mul]
  calc
    _ ≤ (32 * eta b) * 1 := mul_le_mul (rawAngle_error b) (sample_ratio_norm hj)
      (norm_nonneg _) (mul_nonneg (by norm_num) (eta_nonneg b))
    _ = _ := mul_one _

theorem rawNode_error {b j : ℕ} (hj : j < nodeCount b) :
    ‖eval (rawNode b j) - sampleNode (nodeCount b) j‖ ≤ epsilon b := by
  let u := mul (rawAngle b) (j, 0, nodeCount b)
  let v := trueAngle * ((j : ℂ) / nodeCount b)
  have hu : Valid u := valid_mul (rawAngle_valid _) (show Valid (j, 0, nodeCount b) from primeNodes_pos _)
  have he : ‖eval u - v‖ ≤ 32 * eta b := rawNodeArgument_error hj
  have hv : ‖v‖ ≤ 8 := by
    dsimp [v]
    rw [norm_mul]
    have := mul_le_mul trueAngle_norm (sample_ratio_norm hj) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    simpa using this
  have hun : ‖eval u‖ ≤ 16 := by
    have ht := norm_le_norm_sub_add (eval u) v
    linarith [eta_thirtytwo_le_one b]
  have hexpn : ‖Complex.exp v‖ = 1 := by
    change ‖Complex.exp (trueAngle * ((j : ℂ) / nodeCount b))‖ = 1
    rw [← sampleRoot_exp, sampleRoot_norm]
  have h₁ := rawExp_error b hu hun
  have h₂ := exp_difference_bound (eval u) v (he.trans (eta_thirtytwo_le_one b))
  rw [hexpn] at h₂
  have ht := norm_sub_le_norm_sub_add_norm_sub (eval (rawExp b u))
    (Complex.exp (eval u)) (Complex.exp v)
  have hf : ‖eval (rawExp b u) - Complex.exp v‖ ≤ epsilon b := by
    have hb := node_error_le_epsilon b
    dsimp only [eta] at hb
    dsimp only [eta] at he
    linarith
  have hid : eval (rawNode b j) - sampleNode (nodeCount b) j =
      (3 / 4 : ℂ) * (eval (rawExp b u) - Complex.exp v) := by
    rw [rawNode_correct, sampleNode, sampleRoot_exp]
    dsimp only [u, v]
    ring
  rw [hid, norm_mul]
  norm_num
  nlinarith [epsilon_nonneg b]

theorem rawNode_disk {b j : ℕ} (hj : j < nodeCount b) :
    ‖eval (rawNode b j) - center‖ ≤ (7 / 8 : ℝ) := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (eval (rawNode b j))
    (sampleNode (nodeCount b) j) center
  rw [sampleNode_distance] at ht
  linarith [rawNode_error hj, epsilon_le_eighth b]

theorem sampleNode_disk (b j : ℕ) : ‖sampleNode (nodeCount b) j - center‖ ≤ (7 / 8 : ℝ) := by
  rw [sampleNode_distance]
  norm_num

theorem rawLogAmplitude_error {b l j : ℕ} (hl : l ≤ b) (hj : j < nodeCount b) :
    ‖eval (rawLogAmplitude b l j) - logAmplitude l (sampleNode (nodeCount b) j)‖ ≤
      ((b : ℝ) + 10) * epsilon b := by
  have htwo := rawLogTwo_error b
  have hlog := rawLog_error b (rawNode_valid b j) (rawNode_disk hj)
  have hlip := log_lipschitz (rawNode_disk hj) (sampleNode_disk b j)
  have he := rawNode_error hj
  have hid : eval (rawLogAmplitude b l j) - logAmplitude l (sampleNode (nodeCount b) j) =
      (l : ℂ) * (eval (rawLogTwo b) - (Real.log 2 : ℂ)) +
      (eval (rawLog b (rawNode b j)) - Complex.log (eval (rawNode b j))) +
      (Complex.log (eval (rawNode b j)) - Complex.log (sampleNode (nodeCount b) j)) := by
    rw [rawLogAmplitude_correct, logAmplitude]
    ring
  rw [hid]
  have h₁ := norm_add_le ((l : ℂ) * (eval (rawLogTwo b) - (Real.log 2 : ℂ)))
    (eval (rawLog b (rawNode b j)) - Complex.log (eval (rawNode b j)))
  have h₂ := norm_add_le
    ((l : ℂ) * (eval (rawLogTwo b) - (Real.log 2 : ℂ)) +
      (eval (rawLog b (rawNode b j)) - Complex.log (eval (rawNode b j))))
    (Complex.log (eval (rawNode b j)) - Complex.log (sampleNode (nodeCount b) j))
  have hs : ‖(l : ℂ) * (eval (rawLogTwo b) - (Real.log 2 : ℂ))‖ ≤
      (b : ℝ) * epsilon b := by
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (l : ℝ) * (4 * eta b) := mul_le_mul_of_nonneg_left htwo (by positivity)
      _ ≤ (b : ℝ) * epsilon b := mul_le_mul (by exact_mod_cast hl)
        (four_eta_le_epsilon b) (mul_nonneg (by norm_num) (eta_nonneg b)) (by positivity)
  change ‖eval (rawLog b (rawNode b j)) - Complex.log (eval (rawNode b j))‖ ≤ 8 * eta b at hlog
  nlinarith [four_eta_le_epsilon b, epsilon_nonneg b]

theorem rawInvLogAmplitude_error {b l j : ℕ} (hl₀ : 1 ≤ l) (hl : l ≤ b) (hj : j < nodeCount b) :
    ‖eval (inv (rawLogAmplitude b l j)) - invLogAmplitude l (sampleNode (nodeCount b) j)‖ ≤
      50 * ((b : ℝ) + 10) * epsilon b := by
  rw [eval_inv (rawLogAmplitude_valid _ _ _)]
  have he := rawLogAmplitude_error hl hj
  have hi := (invLog_perturbation hl₀ (sampleNode_disk b j)
    (he.trans (amplitude_epsilon_le_tenth b))).2
  nlinarith

theorem sampleNode_sub_one (b j : ℕ) :
    ‖sampleNode (nodeCount b) j - 1‖ ≤ (5 / 4 : ℝ) := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (sampleNode (nodeCount b) j) center 1
  rw [sampleNode_distance] at ht
  norm_num [center] at ht
  exact ht

theorem rawPhaseArgument_error {b j : ℕ} (hj : j < nodeCount b) :
    ‖eval (mul (rawAngle b) (add (rawNode b j) (ofInt (-1)))) -
      trueAngle * (sampleNode (nodeCount b) j - 1)‖ ≤ 12 * epsilon b := by
  have hid : eval (mul (rawAngle b) (add (rawNode b j) (ofInt (-1)))) -
      trueAngle * (sampleNode (nodeCount b) j - 1) =
      eval (rawAngle b) * (eval (rawNode b j) - sampleNode (nodeCount b) j) +
      (eval (rawAngle b) - trueAngle) * (sampleNode (nodeCount b) j - 1) := by
    rw [rawPhaseArgument_correct]
    ring
  rw [hid]
  have h₁ : ‖eval (rawAngle b) * (eval (rawNode b j) - sampleNode (nodeCount b) j)‖ ≤
      9 * epsilon b := by
    rw [norm_mul]
    exact mul_le_mul (rawAngle_norm b) (rawNode_error hj) (norm_nonneg _) (by norm_num)
  have h₂ : ‖(eval (rawAngle b) - trueAngle) * (sampleNode (nodeCount b) j - 1)‖ ≤
      40 * eta b := by
    rw [norm_mul]
    have h := mul_le_mul (rawAngle_error b) (sampleNode_sub_one b j) (norm_nonneg _)
      (mul_nonneg (by norm_num) (eta_nonneg b))
    nlinarith
  have ht := norm_add_le
    (eval (rawAngle b) * (eval (rawNode b j) - sampleNode (nodeCount b) j))
    ((eval (rawAngle b) - trueAngle) * (sampleNode (nodeCount b) j - 1))
  nlinarith [thirtytwo_eta_le_epsilon b, epsilon_nonneg b]

theorem rawPhase_error {b j : ℕ} (hj : j < nodeCount b) :
    ‖eval (rawPhase b j) - shiftedPhase (sampleNode (nodeCount b) j)‖ ≤
      (2 : ℝ) ^ 20 * epsilon b := by
  let u := mul (rawAngle b) (add (rawNode b j) (ofInt (-1)))
  let v := trueAngle * (sampleNode (nodeCount b) j - 1)
  have hu : Valid u := valid_mul (rawAngle_valid _) (valid_add (rawNode_valid _ _) (valid_ofInt _))
  have he : ‖eval u - v‖ ≤ 12 * epsilon b := rawPhaseArgument_error hj
  have hv : ‖v‖ ≤ 10 := by
    dsimp [v]
    rw [norm_mul]
    have h := mul_le_mul trueAngle_norm (sampleNode_sub_one b j) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith
  have hun : ‖eval u‖ ≤ 16 := by
    have ht := norm_le_norm_sub_add (eval u) v
    linarith [twelve_epsilon_le_one b]
  have hexp : Complex.exp v = shiftedPhase (sampleNode (nodeCount b) j) := by
    simp only [v, trueAngle, shiftedPhase]
  have hexpn : ‖Complex.exp v‖ ≤ 2187 := by
    rw [hexp]
    exact (shiftedPhase_bound (sampleNode_disk b j)).trans phase_exp_bound
  have h₁ := rawExp_error b hu hun
  have h₂ := exp_difference_bound (eval u) v (he.trans (twelve_epsilon_le_one b))
  have hp : 2 * ‖Complex.exp v‖ * ‖eval u - v‖ ≤ 2 * 2187 * (12 * epsilon b) := by
    gcongr
  have ht := norm_sub_le_norm_sub_add_norm_sub (eval (rawExp b u))
    (Complex.exp (eval u)) (Complex.exp v)
  change ‖eval (rawExp b u) - Complex.exp (eval u)‖ ≤ (2 : ℝ) ^ 125 * eta b at h₁
  change ‖eval (rawExp b u) - shiftedPhase (sampleNode (nodeCount b) j)‖ ≤ _
  rw [← hexp]
  have hb := node_error_le_epsilon b
  norm_num at hb ⊢
  nlinarith [eta_nonneg b, epsilon_nonneg b]

theorem rawResidue_error {b j : ℕ} (hj : j < nodeCount b) {f : Raw} (hf : Valid f)
    {F : ℂ → ℂ} {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (he : ‖eval f - F (sampleNode (nodeCount b) j)‖ ≤ A)
    (hn : ‖F (sampleNode (nodeCount b) j)‖ ≤ H) :
    ‖eval (rawResidue b j f) - sampleResidue (nodeCount b) j F‖ ≤ A + H * epsilon b := by
  have hid : eval (rawResidue b j f) - sampleResidue (nodeCount b) j F =
      (eval f - F (sampleNode (nodeCount b) j)) * (eval (rawNode b j) - center) +
      F (sampleNode (nodeCount b) j) * (eval (rawNode b j) - sampleNode (nodeCount b) j) := by
    rw [rawResidue_correct _ _ hf, sampleResidue]
    ring
  rw [hid]
  have h₁ : ‖(eval f - F (sampleNode (nodeCount b) j)) * (eval (rawNode b j) - center)‖ ≤ A := by
    rw [norm_mul]
    calc
      _ ≤ A * 1 := mul_le_mul he ((rawNode_disk hj).trans (by norm_num)) (norm_nonneg _) hA
      _ = _ := mul_one _
  have h₂ : ‖F (sampleNode (nodeCount b) j) * (eval (rawNode b j) - sampleNode (nodeCount b) j)‖ ≤
      H * epsilon b := by
    rw [norm_mul]
    exact mul_le_mul hn (rawNode_error hj) (norm_nonneg _) hH
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

theorem rounded_error (p : ℕ) (z : Raw) (w : ℂ)
    (he : ‖eval z - w‖ ≤ 1 / (2 : ℝ) ^ p) :
    ‖value p (nearest p z) - w‖ ≤ 2 / (2 : ℝ) ^ p := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (value p (nearest p z)) (eval z) w
  have hn := nearest_error p z
  change ‖value p (nearest p z) - eval z‖ ≤ 1 / (2 : ℝ) ^ p at hn
  calc
    _ ≤ 1 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ p := ht.trans (add_le_add hn he)
    _ = _ := by ring

theorem pole_error {b j : ℕ} (hj : j < nodeCount b) :
    ‖value (coefficientBits b) (pole b j) - sampleNode (nodeCount b) j‖ ≤
      2 / (2 : ℝ) ^ coefficientBits b :=
  rounded_error _ _ _ ((rawNode_error hj).trans (epsilon_le_coefficient_unit b))

theorem logResidue_error {b l j : ℕ} (hl : l ≤ b) (hj : j < nodeCount b) :
    ‖value (coefficientBits b) (logResidue b l j) -
      sampleResidue (nodeCount b) j (logAmplitude l)‖ ≤
      2 / (2 : ℝ) ^ coefficientBits b := by
  apply rounded_error
  have hbound : ‖logAmplitude l (sampleNode (nodeCount b) j)‖ ≤ (b : ℝ) + 6 := by
    have h := logAmplitude_norm_le l (sampleNode_disk b j)
    have hr : (l : ℝ) ≤ b := by exact_mod_cast hl
    linarith
  have he := rawResidue_error hj (rawLogAmplitude_valid b l j)
    (mul_nonneg (by positivity) (epsilon_nonneg b)) (by positivity)
    (rawLogAmplitude_error hl hj) hbound
  apply he.trans
  apply (le_trans ?_ (final_error_budget b))
  have hp := epsilon_nonneg b
  have hb : (0 : ℝ) ≤ b := by positivity
  norm_num
  nlinarith [mul_nonneg hb hp]

theorem invLogResidue_error {b l j : ℕ} (hl₀ : 1 ≤ l) (hl : l ≤ b) (hj : j < nodeCount b) :
    ‖value (coefficientBits b) (invLogResidue b l j) -
      sampleResidue (nodeCount b) j (invLogAmplitude l)‖ ≤
      2 / (2 : ℝ) ^ coefficientBits b := by
  apply rounded_error
  have hbound : ‖invLogAmplitude l (sampleNode (nodeCount b) j)‖ ≤ (5 : ℝ) :=
    (invLogAmplitude_norm_le hl₀ (sampleNode_disk b j)).trans inverse_log_bound
  have he := rawResidue_error hj (valid_inv (rawLogAmplitude b l j))
    (mul_nonneg (by positivity) (epsilon_nonneg b)) (by norm_num)
    (rawInvLogAmplitude_error hl₀ hl hj) hbound
  apply he.trans
  apply (le_trans ?_ (final_error_budget b))
  have hp := epsilon_nonneg b
  have hb : (0 : ℝ) ≤ b := by positivity
  norm_num
  nlinarith [mul_nonneg hb hp]

theorem phaseResidue_error {b j : ℕ} (hj : j < nodeCount b) :
    ‖value (coefficientBits b) (phaseResidue b j) -
      sampleResidue (nodeCount b) j shiftedPhase‖ ≤
      2 / (2 : ℝ) ^ coefficientBits b := by
  apply rounded_error
  have hbound : ‖shiftedPhase (sampleNode (nodeCount b) j)‖ ≤ (2187 : ℝ) :=
    (shiftedPhase_bound (sampleNode_disk b j)).trans phase_exp_bound
  have he := rawResidue_error hj (rawPhase_valid b j)
    (mul_nonneg (by positivity) (epsilon_nonneg b)) (by norm_num)
    (rawPhase_error hj) hbound
  apply he.trans
  apply (le_trans ?_ (final_error_budget b))
  have hp := epsilon_nonneg b
  have hb : (0 : ℝ) ≤ b := by positivity
  norm_num
  nlinarith [mul_nonneg hb hp]

/-- This certificate is produced by concrete integer algorithms, without any
oracle for exact transcendental rounding and without an error hypothesis. -/
theorem generate_certified (b : ℕ) : Certified b (generate b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    exact ⟨fun j hj => pole_error (mem_range.mp hj),
      fun j hj => logResidue_error hl (mem_range.mp hj)⟩
  · intro l hl₀ hl
    exact ⟨fun j hj => pole_error (mem_range.mp hj),
      fun j hj => invLogResidue_error hl₀ hl (mem_range.mp hj)⟩
  · exact ⟨fun j hj => pole_error (mem_range.mp hj),
      fun j hj => phaseResidue_error (mem_range.mp hj)⟩

theorem generatedPrimeSum_all_inputs (N : ℕ) :
    ⌊(approximatePrimeSum (Nat.log 2 N + 1) (generate (Nat.log 2 N + 1)) N).re + 1 / 2⌋ =
      (primeSum N : ℤ) :=
  primeSum_all_inputs N (generate (Nat.log 2 N + 1)) (generate_certified _)

end PrimeAlgorithm.CertifiedGenerator
