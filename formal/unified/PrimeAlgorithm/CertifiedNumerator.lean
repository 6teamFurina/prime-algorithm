import PrimeAlgorithm.CertifiedCauchy
import PrimeAlgorithm.ReciprocalKernelSigns

/-! A computable integer numerator for the certified rational Cauchy evaluator.
No transcendental quantity or real-number floor is read by these definitions. -/
namespace PrimeAlgorithm.CertifiedNumerator

open Finset PrimeAlgorithm.CertifiedCauchy PrimeAlgorithm.SignedQuantization
  PrimeAlgorithm.Cauchy

def embed (z : GaussianIntPair) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

def multiply (z w : GaussianIntPair) : GaussianIntPair :=
  (z.1*w.1-z.2*w.2, z.1*w.2+z.2*w.1)

def signedQuotient (t : ℕ) (a : ℤ) (D : ℕ) : ℤ :=
  if a < 0 then -((2^t*a.natAbs/D : ℕ) : ℤ) else (2^t*a.natAbs/D : ℕ)

theorem signedQuotient_spec (t : ℕ) (a : ℤ) (D : ℕ) :
    truncateReal t ((a : ℝ)/D) = (signedQuotient t a D : ℝ)/(2:ℝ)^t := by
  by_cases ha : a < 0
  · have he : a = -(a.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_neg ha]; ring
    rw [signedQuotient, if_pos ha, Int.cast_neg, Int.cast_natCast]
    conv_lhs => rw [he, Int.cast_neg, Int.cast_natCast, neg_div]
    simpa only [neg_div] using truncateReal_neg_nat_div t a.natAbs D
  · have he : a = (a.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt ha)]
    rw [signedQuotient, if_neg ha, Int.cast_natCast]
    conv_lhs => rw [he, Int.cast_natCast]
    exact truncateReal_nat_div t a.natAbs D

theorem truncateComplex_int_div (t : ℕ) (a b : ℤ) (D : ℕ) :
    truncateComplex t ⟨(a:ℝ)/D,(b:ℝ)/D⟩ =
      embed (signedQuotient t a D, signedQuotient t b D) / (2:ℂ)^t := by
  rw [show (2:ℂ)^t = Complex.ofReal ((2:ℝ)^t) by simp]
  apply Complex.ext <;>
    simp only [truncateComplex, embed, Complex.div_ofReal_re, Complex.div_ofReal_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
      zero_add, add_zero, sub_zero, signedQuotient_spec]

theorem embed_multiply (z w : GaussianIntPair) : embed (multiply z w) = embed z * embed w := by
  apply Complex.ext <;> simp [embed, multiply, Complex.mul_re, Complex.mul_im] <;> ring

def horizontal (p : ℕ) (z : GaussianIntPair) (num den : ℕ) : ℤ :=
  z.1*den-(2^p:ℤ)*num

def vertical (z : GaussianIntPair) (den : ℕ) : ℤ := z.2*den

def denominator (p : ℕ) (z : GaussianIntPair) (num den : ℕ) : ℕ :=
  (horizontal p z num den).natAbs^2 + (vertical z den).natAbs^2

def reciprocalNumerator (p t : ℕ) (z : GaussianIntPair) (num den : ℕ) : GaussianIntPair :=
  let D := denominator p z num den
  (signedQuotient t ((2^p:ℤ)*den*horizontal p z num den) D,
   signedQuotient t (-((2^p:ℤ)*den*vertical z den)) D)

def numerator (p t M : ℕ) (D : Data) (num den : ℕ) : GaussianIntPair :=
  ∑ j ∈ range M, multiply (D.residue j) (reciprocalNumerator p t (D.pole j) num den)

def scale (p t M : ℕ) : ℕ := M*2^(p+t)

theorem denominator_cast (p : ℕ) (z : GaussianIntPair) (num den : ℕ) :
    (denominator p z num den : ℝ) =
      (horizontal p z num den : ℝ)^2 + (vertical z den : ℝ)^2 := by
  simp [denominator, Nat.cast_natAbs, Int.cast_abs, sq_abs]

theorem reciprocal_spec (p t : ℕ) (z : GaussianIntPair) (num den : ℕ) (hd : 0 < den) :
    truncateComplex t (1 / (value p z - (num : ℂ)/den)) =
      embed (reciprocalNumerator p t z num den) / (2 : ℂ)^t := by
  have h := reciprocal_scaled_formula (z.1 : ℝ) (z.2 : ℝ) ((2:ℝ)^p)
    (den : ℝ) (num : ℝ) (by positivity) (by positivity)
  have hv : value p z = (((z.1:ℝ):ℂ)+((z.2:ℝ):ℂ)*Complex.I)/((2:ℝ)^p:ℂ) := by
    simp [value]
  have hh : (horizontal p z num den : ℝ) = (z.1:ℝ)*den-(2:ℝ)^p*num := by
    simp [horizontal]
  have hy : (vertical z den : ℝ) = (z.2:ℝ)*den := by simp [vertical]
  have ha : (((2^p:ℤ)*den*horizontal p z num den : ℤ):ℝ) =
      (2:ℝ)^p*den*((z.1:ℝ)*den-(2:ℝ)^p*num) := by simp [hh]
  have hb : ((-((2^p:ℤ)*den*vertical z den):ℤ):ℝ) =
      -((2:ℝ)^p*den*((z.2:ℝ)*den)) := by simp [hy]
  have hD : (denominator p z num den : ℝ) =
      ((z.1:ℝ)*den-(2:ℝ)^p*num)^2 + ((z.2:ℝ)*den)^2 := by
    rw [denominator_cast, hh, hy]
  have hr : 1 / (value p z - (num:ℂ)/den) =
      (⟨(((2^p:ℤ)*den*horizontal p z num den : ℤ):ℝ)/(denominator p z num den),
       ((-((2^p:ℤ)*den*vertical z den):ℤ):ℝ)/(denominator p z num den)⟩ : ℂ) := by
    rw [hv]
    simp only [Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_intCast,
      Complex.ofReal_ofNat] at h ⊢
    rw [h]
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        zero_mul, zero_add, add_zero, sub_zero, zero_sub] <;>
      rw [hD] <;> simp only [ha, hb, neg_div]
  rw [hr]
  exact truncateComplex_int_div t _ _ _

theorem numerator_spec (p t M : ℕ) (D : Data) (num den : ℕ) (hd : 0 < den) :
    evaluate p t M D ((num : ℂ)/den) =
      embed (numerator p t M D num den) / (scale p t M : ℂ) := by
  unfold evaluate
  simp_rw [reciprocal_spec p t _ num den hd]
  have he (j : ℕ) : value p (D.residue j) *
      (embed (reciprocalNumerator p t (D.pole j) num den)/(2:ℂ)^t) =
      embed (multiply (D.residue j) (reciprocalNumerator p t (D.pole j) num den)) /
        (2:ℂ)^(p+t) := by
    rw [value, embed_multiply, pow_add]
    unfold embed
    ring
  simp_rw [he]
  rw [← sum_div]
  have hs : (∑ j ∈ range M,
      embed (multiply (D.residue j) (reciprocalNumerator p t (D.pole j) num den))) =
      embed (numerator p t M D num den) := by
    simp [embed, numerator, Prod.fst_sum, Prod.snd_sum, Int.cast_sum, sum_mul, sum_add_distrib]
  rw [hs, div_div, scale]
  push_cast
  ring

end PrimeAlgorithm.CertifiedNumerator
