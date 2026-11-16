import PrimeAlgorithm.CertifiedPrimeSum
import PrimeAlgorithm.CertifiedNumerator

/-! Certified coefficient tables have linear bit length. These bounds apply
to the actual integer coordinates delivered by any certified generator. -/

namespace PrimeAlgorithm.CertifiedCoordinateBounds
open Finset PrimeAlgorithm.CertifiedCauchy PrimeAlgorithm.Cauchy

theorem value_re (p : ℕ) (z : GaussianIntPair) :
    (value p z).re = (z.1:ℝ)/(2:ℝ)^p := by
  unfold value
  rw [show (2:ℂ)^p = Complex.ofReal ((2:ℝ)^p) by simp]
  simp only [Complex.div_ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero]

theorem value_im (p : ℕ) (z : GaussianIntPair) :
    (value p z).im = (z.2:ℝ)/(2:ℝ)^p := by
  unfold value
  rw [show (2:ℂ)^p = Complex.ofReal ((2:ℝ)^p) by simp]
  simp only [Complex.div_ofReal_im, Complex.add_im, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, zero_add, add_zero]

theorem coordinate_norm_bound (p : ℕ) (z : GaussianIntPair) {H : ℝ}
    (h : ‖value p z‖ ≤ H) :
    (z.1.natAbs:ℝ) ≤ H*(2:ℝ)^p ∧ (z.2.natAbs:ℝ) ≤ H*(2:ℝ)^p := by
  have hr := (Complex.abs_re_le_norm (value p z)).trans h
  have hi := (Complex.abs_im_le_norm (value p z)).trans h
  rw [value_re, abs_div, abs_of_pos (by positivity : (0:ℝ)<2^p)] at hr
  rw [value_im, abs_div, abs_of_pos (by positivity : (0:ℝ)<2^p)] at hi
  constructor
  · simpa only [Nat.cast_natAbs, Int.cast_abs] using (div_le_iff₀ (by positivity)).mp hr
  · simpa only [Nat.cast_natAbs, Int.cast_abs] using (div_le_iff₀ (by positivity)).mp hi

def inputBits (b : ℕ) : ℕ := 8*b+45

theorem magnitude_budget (b : ℕ) :
    ((b:ℝ)+2196)*(2:ℝ)^(coefficientBits b) < (2:ℝ)^inputBits b := by
  have hb : (b:ℝ) ≤ (2:ℝ)^b := by exact_mod_cast (Nat.lt_two_pow_self (n:=b)).le
  have ht : (1:ℝ) ≤ (2:ℝ)^b := one_le_pow₀ (by norm_num)
  have hh : (b:ℝ)+2196 < (2:ℝ)^(b+13) := by
    rw [pow_add]
    norm_num
    linarith
  calc
    _ < (2:ℝ)^(b+13)*(2:ℝ)^(coefficientBits b) :=
      mul_lt_mul_of_pos_right hh (by positivity)
    _ = _ := by
      rw [← pow_add]
      congr 1
      unfold coefficientBits dyadicBits inputBits
      omega

theorem coordinate_bit_bound {b : ℕ} {z : GaussianIntPair}
    (h : ‖value (coefficientBits b) z‖ ≤ (b:ℝ)+2196) :
    z.1.natAbs < 2^inputBits b ∧ z.2.natAbs < 2^inputBits b := by
  obtain ⟨hr,hi⟩ := coordinate_norm_bound (coefficientBits b) z h
  constructor
  · exact_mod_cast hr.trans_lt (magnitude_budget b)
  · exact_mod_cast hi.trans_lt (magnitude_budget b)

theorem sampleNode_norm (M j : ℕ) : ‖sampleNode M j‖ ≤ (9/4:ℝ) := by
  have h := norm_le_norm_sub_add (sampleNode M j) center
  rw [sampleNode_distance] at h
  norm_num [center] at h
  exact h

theorem pole_norm_bound {b : ℕ} {f : ℂ → ℂ} {D : Data}
    (hD : Accurate (coefficientBits b) (nodeCount b) f D)
    {j : ℕ} (hj : j ∈ range (nodeCount b)) : ‖value (coefficientBits b) (D.pole j)‖ ≤ 3 := by
  have h := norm_le_norm_sub_add (value (coefficientBits b) (D.pole j))
    (sampleNode (nodeCount b) j)
  have he := hD.pole_error j hj
  have hs := dyadicBits_small (b+1)
  change 2/(2:ℝ)^coefficientBits b ≤ 1/8 at hs
  linarith [sampleNode_norm (nodeCount b) j]

theorem pole_separation {b : ℕ} {f : ℂ → ℂ} {D : Data}
    (hD : Accurate (coefficientBits b) (nodeCount b) f D)
    {j : ℕ} (hj : j ∈ range (nodeCount b)) {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    (1/8:ℝ) ≤ ‖value (coefficientBits b) (D.pole j) - y‖ := by
  have he := hD.pole_error j hj
  have hs := dyadicBits_small (b+1)
  change 2/(2:ℝ)^coefficientBits b ≤ 1/8 at hs
  have ht := norm_sub_le_norm_sub_add_norm_sub (sampleNode (nodeCount b) j)
    (value (coefficientBits b) (D.pole j)) (y:ℂ)
  rw [norm_sub_rev (sampleNode (nodeCount b) j) (value (coefficientBits b) (D.pole j))] at ht
  linarith [sampleNode_separation (nodeCount b) j hy]

theorem pole_real_positive {b : ℕ} {f : ℂ → ℂ} {D : Data}
    (hD : Accurate (coefficientBits b) (nodeCount b) f D)
    {j : ℕ} (hj : j ∈ range (nodeCount b)) : 0 < (D.pole j).1 := by
  have hn := Complex.abs_re_le_norm (sampleNode (nodeCount b) j - center)
  rw [sampleNode_distance] at hn
  simp only [Complex.sub_re, center, Complex.ofReal_re] at hn
  have hn' := (abs_le.mp hn).1
  have he := (Complex.abs_re_le_norm
    (value (coefficientBits b) (D.pole j) - sampleNode (nodeCount b) j)).trans
    (hD.pole_error j hj)
  have hs := dyadicBits_small (b+1)
  change 2/(2:ℝ)^coefficientBits b ≤ 1/8 at hs
  have he' := (abs_le.mp (he.trans hs)).1
  simp only [Complex.sub_re] at he'
  have hp : 0 < (value (coefficientBits b) (D.pole j)).re := by linarith
  rw [value_re] at hp
  have hi : (0:ℝ) < ((D.pole j).1:ℝ) :=
    (div_pos_iff_of_pos_right (by positivity)).mp hp
  exact_mod_cast hi

theorem pole_bit_bound {b : ℕ} {f : ℂ → ℂ} {D : Data}
    (hD : Accurate (coefficientBits b) (nodeCount b) f D)
    {j : ℕ} (hj : j ∈ range (nodeCount b)) :
    (D.pole j).1.natAbs < 2^inputBits b ∧ (D.pole j).2.natAbs < 2^inputBits b := by
  apply coordinate_bit_bound
  have hb : (0:ℝ)≤b := by positivity
  exact (pole_norm_bound hD hj).trans (by linarith)

theorem residue_bit_bound {b : ℕ} {f : ℂ → ℂ} {D : Data}
    (hD : Accurate (coefficientBits b) (nodeCount b) f D)
    (hf : ∀ j ∈ range (nodeCount b), ‖f (sampleNode (nodeCount b) j)‖ ≤ (b:ℝ)+2195)
    {j : ℕ} (hj : j ∈ range (nodeCount b)) :
    (D.residue j).1.natAbs < 2^inputBits b ∧ (D.residue j).2.natAbs < 2^inputBits b :=
  coordinate_bit_bound (CertifiedCauchy.residue_bound hD hf hj)

theorem denominator_pos_of_ne (p : ℕ) (z : GaussianIntPair) (num den : ℕ)
    (hd : 0 < den) (hne : value p z ≠ (num:ℂ)/den) :
    0 < CertifiedNumerator.denominator p z num den := by
  by_contra h
  have h0 : CertifiedNumerator.denominator p z num den = 0 := by omega
  unfold CertifiedNumerator.denominator at h0
  have hx : CertifiedNumerator.horizontal p z num den = 0 := by
    apply Int.natAbs_eq_zero.mp
    nlinarith
  have hy : CertifiedNumerator.vertical z den = 0 := by
    apply Int.natAbs_eq_zero.mp
    nlinarith
  have hx' : (z.1:ℂ)*den-(2:ℂ)^p*num = 0 := by
    have := congrArg (fun a : ℤ => (a:ℂ)) hx
    simpa [CertifiedNumerator.horizontal] using this
  have hy' : (z.2:ℂ)*den = 0 := by
    have := congrArg (fun a : ℤ => (a:ℂ)) hy
    simpa [CertifiedNumerator.vertical] using this
  apply hne
  unfold value
  have hdc : (den:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  calc
    _ = (z.1:ℂ)*den + ((z.2:ℂ)*den)*Complex.I := by ring
    _ = (2:ℂ)^p*num := by rw [hy']; linear_combination hx'
    _ = _ := by ring

theorem certified_denominator_positive {b : ℕ} {f : ℂ → ℂ} {D : Data}
    (hD : Accurate (coefficientBits b) (nodeCount b) f D)
    {j : ℕ} (hj : j ∈ range (nodeCount b)) {num den : ℕ} (hd : 0 < den)
    (hy : (num:ℝ)/den ∈ Set.Icc 1 2) :
    0 < CertifiedNumerator.denominator (coefficientBits b) (D.pole j) num den := by
  apply denominator_pos_of_ne _ _ _ _ hd
  intro he
  have hsep := pole_separation hD hj hy
  have he' : value (coefficientBits b) (D.pole j) = Complex.ofReal ((num:ℝ)/den) := by
    simpa using he
  rw [he'] at hsep
  norm_num at hsep

end PrimeAlgorithm.CertifiedCoordinateBounds
