import Mathlib

/-! Exact rational Cauchy kernels, circle separation, and integer quotient error.
These statements are uniform in the real argument and the precision. They do
not assume the Cauchy quadrature error theorem. -/

noncomputable section

namespace PrimeAlgorithm.Cauchy

def center : ℂ := ((3 / 2 : ℝ) : ℂ)

def node (θ : ℝ) : ℂ := center + (3 / 4 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

theorem node_distance (θ : ℝ) : ‖node θ - center‖ = (3 / 4 : ℝ) := by
  simp [node, norm_mul, Complex.norm_exp]

theorem interval_distance {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖(y : ℂ) - center‖ ≤ (1 / 2 : ℝ) := by
  have h : |y - 3 / 2| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  change ‖(y : ℂ) - ((3 / 2 : ℝ) : ℂ)‖ ≤ (1 / 2 : ℝ)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h

theorem node_separation (θ : ℝ) {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    (1 / 4 : ℝ) ≤ ‖node θ - y‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub (node θ) (y : ℂ) center
  rw [node_distance] at h
  have := interval_distance hy
  linarith

theorem perturbed_separation (θ : ℝ) {y : ℝ} (hy : y ∈ Set.Icc 1 2)
    {z : ℂ} (hz : ‖z - node θ‖ ≤ (1 / 8 : ℝ)) :
    (1 / 8 : ℝ) ≤ ‖z - y‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub (node θ) z (y : ℂ)
  rw [norm_sub_rev (node θ) z] at h
  have := node_separation θ hy
  linarith

theorem kernel_formula (U V T C : ℝ) :
    ((U : ℂ) + V * Complex.I - C) / ((U : ℂ) + V * Complex.I - T) =
      (((((U - C) * (U - T) + V ^ 2) / ((U - T) ^ 2 + V ^ 2)) : ℝ) : ℂ) +
      (((V * (C - T) / ((U - T) ^ 2 + V ^ 2)) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp only [Complex.div_re, Complex.div_im, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.normSq_apply,
      zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero, zero_sub] <;> ring

theorem kernel_scaled_formula (U V T C Q : ℝ) (hQ : Q ≠ 0) :
    (((U : ℂ) + V * Complex.I) / Q - (C : ℂ) / Q) /
      (((U : ℂ) + V * Complex.I) / Q - (T : ℂ) / Q) =
      (((((U - C) * (U - T) + V ^ 2) / ((U - T) ^ 2 + V ^ 2)) : ℝ) : ℂ) +
      (((V * (C - T) / ((U - T) ^ 2 + V ^ 2)) : ℝ) : ℂ) * Complex.I := by
  have hQ' : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ
  rw [← sub_div, ← sub_div, div_div_div_cancel_right₀ hQ']
  exact kernel_formula U V T C

theorem denominator_eq_norm_sq (U V T : ℝ) :
    (U - T) ^ 2 + V ^ 2 = ‖(U : ℂ) + V * Complex.I - T‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

theorem denominator_lower_bound (U V T δ : ℝ)
    (hδ : 0 ≤ δ) (h : δ ≤ ‖(U : ℂ) + V * Complex.I - T‖) :
    δ ^ 2 ≤ (U - T) ^ 2 + V ^ 2 := by
  rw [denominator_eq_norm_sq]
  exact pow_le_pow_left₀ hδ h 2

theorem nat_quotient_error (A D : ℕ) (hD : 0 < D) :
    0 ≤ (A : ℝ) / D - (A / D : ℕ) ∧
    (A : ℝ) / D - (A / D : ℕ) < 1 := by
  have hrealD : (0 : ℝ) < D := by exact_mod_cast hD
  have hrem : ((A % D : ℕ) : ℝ) < D := by exact_mod_cast Nat.mod_lt A hD
  have hnonneg : (0 : ℝ) ≤ ((A % D : ℕ) : ℝ) := by positivity
  have hid : (A : ℝ) = (A / D : ℕ) * (D : ℝ) + ((A % D : ℕ) : ℝ) := by
    exact_mod_cast (show A = A / D * D + A % D by simpa [Nat.mul_comm] using (Nat.div_add_mod A D).symm)
  have heq : (A : ℝ) / D - (A / D : ℕ) = ((A % D : ℕ) : ℝ) / D := by
    apply (eq_div_iff hrealD.ne').mpr
    rw [sub_mul, div_mul_cancel₀ _ hrealD.ne']
    linarith
  rw [heq]
  exact ⟨div_nonneg hnonneg hrealD.le, (div_lt_one hrealD).mpr hrem⟩

theorem scaled_nat_quotient_error (A D P : ℕ) (hD : 0 < D) (hP : 0 < P) :
    0 ≤ (A : ℝ) / (P * D) - (A / D : ℕ) / P ∧
    (A : ℝ) / (P * D) - (A / D : ℕ) / P < 1 / P := by
  have h := nat_quotient_error A D hD
  have hrealP : (0 : ℝ) < P := by exact_mod_cast hP
  have hrealD : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have heq : (A : ℝ) / (P * D) - (A / D : ℕ) / P =
      ((A : ℝ) / D - (A / D : ℕ)) / P := by
    field_simp
  rw [heq]
  exact ⟨div_nonneg h.1 hrealP.le, (div_lt_div_iff_of_pos_right hrealP).mpr h.2⟩

end PrimeAlgorithm.Cauchy
