import PrimeAlgorithm.CauchyKernel
import PrimeAlgorithm.SignedQuantization

/-! Exact sign and quotient interfaces for the reciprocal Cauchy components.
The imaginary reciprocal sign is opposite to the imaginary pole sign.
No assertion of an assembled arithmetic network is made in this module. -/

noncomputable section
namespace PrimeAlgorithm.Cauchy

open PrimeAlgorithm.PhaseApproximation PrimeAlgorithm.SignedQuantization

/-- Reciprocal of a pole with a signed imaginary coordinate and a rational input. -/
theorem reciprocal_scaled_formula (U V Q d t : ℝ) (hQ : Q≠0) (hd : d≠0) :
    1 / (((U : ℂ) + V*Complex.I) / Q - (t : ℂ)/d) =
      ((Q*d*(U*d-Q*t)/((U*d-Q*t)^2+(V*d)^2) : ℝ) : ℂ) -
      ((Q*d*(V*d)/((U*d-Q*t)^2+(V*d)^2) : ℝ) : ℂ)*Complex.I := by
  have hQc : (Q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ
  have hdc : (d : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hd
  have he : ((U : ℂ)+V*Complex.I)/Q-(t : ℂ)/d =
      (((U*d-Q*t : ℝ) : ℂ)+(V*d : ℝ)*Complex.I)/(Q*d : ℝ) := by
    push_cast
    field_simp
    ring
  rw [he,one_div_div]
  apply Complex.ext <;>
    simp only [Complex.div_re,Complex.div_im,Complex.add_re,Complex.sub_re,
      Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.I_im,Complex.add_im,
      Complex.sub_im,Complex.mul_im,Complex.ofReal_im,Complex.normSq_apply,
      zero_mul,mul_zero,mul_one,zero_add,add_zero,sub_zero,zero_sub] <;> ring

/-- Dyadic floor of a nonnegative rational number is an actual natural quotient. -/
theorem quantizeReal_nat_div (p A D : ℕ) :
    quantizeReal p ((A : ℝ)/D) = ((2^p*A/D : ℕ) : ℝ)/(2:ℝ)^p := by
  unfold quantizeReal
  have he : (2:ℝ)^p*((A:ℝ)/D) = ((2^p*A : ℕ):ℝ)/D := by push_cast; ring
  rw [he,Int.floor_div_natCast,Int.floor_natCast]
  congr 1

/-- Toward-zero quantization agrees with the positive quotient count. -/
theorem truncateReal_nat_div (p A D : ℕ) :
    truncateReal p ((A : ℝ)/D) = ((2^p*A/D : ℕ) : ℝ)/(2:ℝ)^p := by
  rw [truncateReal,if_pos (by positivity)]
  exact quantizeReal_nat_div p A D

/-- Negative components are exactly the negative positive-magnitude count. -/
theorem truncateReal_neg_nat_div (p A D : ℕ) :
    truncateReal p (-((A : ℝ)/D)) = -(((2^p*A/D : ℕ) : ℝ)/(2:ℝ)^p) := by
  rw [truncateReal_neg,truncateReal_nat_div]

/-- Real and imaginary signs are independent; these are the two magnitudes
    counted by separate real/imaginary kernel descriptors. -/
theorem truncateComplex_signed_nat_div (p A B D : ℕ) (realNeg imagNeg : Bool) :
    truncateComplex p
      ⟨if realNeg then -((A:ℝ)/D) else (A:ℝ)/D,
       if imagNeg then -((B:ℝ)/D) else (B:ℝ)/D⟩ =
      ⟨if realNeg then -(((2^p*A/D:ℕ):ℝ)/(2:ℝ)^p)
         else ((2^p*A/D:ℕ):ℝ)/(2:ℝ)^p,
       if imagNeg then -(((2^p*B/D:ℕ):ℝ)/(2:ℝ)^p)
         else ((2^p*B/D:ℕ):ℝ)/(2:ℝ)^p⟩ := by
  cases realNeg <;> cases imagNeg <;>
    simp [truncateComplex,truncateReal_nat_div,truncateReal_neg_nat_div]

end PrimeAlgorithm.Cauchy
