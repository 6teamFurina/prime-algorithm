module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

public section

namespace PrimeAlgorithm.PhaseApproximation

open Finset

/-- Quantized products are compared before summing any tensor-path states. -/
theorem product_error (f g : ℕ → ℂ) (ε : ℝ) (_hε : 0 ≤ ε) (n : ℕ)
    (hg : ∀ j < n, ‖g j‖ = 1) (he : ∀ j < n, ‖f j - g j‖ ≤ ε) :
    ‖(∏ j ∈ range n, f j) - ∏ j ∈ range n, g j‖ ≤ (1 + ε) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hgn := hg n (by omega)
    have hen := he n (by omega)
    have hip := ih (fun j hj => hg j (by omega)) (fun j hj => he j (by omega))
    have hfn : ‖f n‖ ≤ 1 + ε := by
      calc
        ‖f n‖ = ‖(f n - g n) + g n‖ := by congr 1; ring
        _ ≤ ‖f n - g n‖ + ‖g n‖ := norm_add_le _ _
        _ ≤ 1 + ε := by rw [hgn]; linarith
    have hgp : ‖∏ j ∈ range n, g j‖ = 1 := by
      rw [norm_prod]
      exact prod_eq_one (fun j hj => hg j (by have := mem_range.1 hj; omega))
    rw [prod_range_succ, prod_range_succ]
    calc
      _ = ‖((∏ j ∈ range n, f j) - ∏ j ∈ range n, g j) * f n +
          (∏ j ∈ range n, g j) * (f n - g n)‖ := by congr 1; ring
      _ ≤ ‖(∏ j ∈ range n, f j) - ∏ j ∈ range n, g j‖ * ‖f n‖ +
          ‖∏ j ∈ range n, g j‖ * ‖f n - g n‖ := by
        simpa only [norm_mul] using norm_add_le
          (((∏ j ∈ range n, f j) - ∏ j ∈ range n, g j) * f n)
          ((∏ j ∈ range n, g j) * (f n - g n))
      _ ≤ ((1 + ε) ^ n - 1) * (1 + ε) + ε := by
        rw [hgp, one_mul]
        have hp0 : 0 ≤ (1 + ε) ^ n - 1 := le_trans (norm_nonneg _) hip
        gcongr
      _ = (1 + ε) ^ (n + 1) - 1 := by rw [pow_succ]; ring

theorem product_error_linear (f g : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (hn : (n : ℝ) * ε ≤ 1)
    (hg : ∀ j < n, ‖g j‖ = 1) (he : ∀ j < n, ‖f j - g j‖ ≤ ε) :
    ‖(∏ j ∈ range n, f j) - ∏ j ∈ range n, g j‖ ≤ 2 * n * ε := by
  have h0 : 0 ≤ (n : ℝ) * ε := by positivity
  have hpow : (1 + ε) ^ n ≤ Real.exp ((n : ℝ) * ε) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ε]) n
  have hexp := Real.abs_exp_sub_one_le (x := (n : ℝ) * ε)
    (by simpa only [abs_of_nonneg h0] using hn)
  rw [abs_of_nonneg h0] at hexp
  have hb := product_error f g ε hε n hg he
  have ha := le_abs_self (Real.exp ((n : ℝ) * ε) - 1)
  nlinarith

noncomputable def unitPhase (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

@[simp] theorem norm_unitPhase (t : ℝ) : ‖unitPhase t‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal t

theorem prod_unitPhase (θ : ℕ → ℝ) (n : ℕ) :
    (∏ j ∈ range n, unitPhase (θ j)) = unitPhase (∑ j ∈ range n, θ j) := by
  induction n with
  | zero => simp [unitPhase]
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, ih]
    simp only [unitPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

noncomputable def quantizeReal (p : ℕ) (x : ℝ) : ℝ :=
  (⌊(2 : ℝ) ^ p * x⌋ : ℤ) / (2 : ℝ) ^ p

/-- Mathematical dyadic quantization; its eventual effective implementation
must use a rational approximation with a certified error. -/
noncomputable def quantizeComplex (p : ℕ) (z : ℂ) : ℂ :=
  ⟨quantizeReal p z.re, quantizeReal p z.im⟩

theorem quantizeReal_error (p : ℕ) (x : ℝ) :
    |quantizeReal p x - x| < 1 / (2 : ℝ) ^ p := by
  have hQ : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hlo := Int.floor_le ((2 : ℝ) ^ p * x)
  have hhi := Int.lt_floor_add_one ((2 : ℝ) ^ p * x)
  unfold quantizeReal
  rw [abs_sub_comm, abs_of_nonneg (by
    apply sub_nonneg.2
    apply (div_le_iff₀ hQ).2
    nlinarith)]
  apply (lt_div_iff₀ hQ).2
  have hcancel := div_mul_cancel₀ (⌊(2 : ℝ) ^ p * x⌋ : ℝ) hQ.ne'
  nlinarith

theorem quantizeComplex_error (p : ℕ) (z : ℂ) :
    ‖quantizeComplex p z - z‖ ≤ 2 / (2 : ℝ) ^ p := by
  have h := Complex.norm_le_abs_re_add_abs_im (quantizeComplex p z - z)
  simp only [quantizeComplex, Complex.sub_re, Complex.sub_im] at h
  have h1 := quantizeReal_error p z.re
  have h2 := quantizeReal_error p z.im
  calc
    _ ≤ |quantizeReal p z.re - z.re| + |quantizeReal p z.im - z.im| := h
    _ ≤ 1 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ p := add_le_add h1.le h2.le
    _ = _ := by ring

theorem quantized_phase_product_error (p n : ℕ) (θ : ℕ → ℝ)
    (hn : (n : ℝ) * (2 / (2 : ℝ) ^ p) ≤ 1) :
    ‖(∏ j ∈ range n, quantizeComplex p (unitPhase (θ j))) -
      unitPhase (∑ j ∈ range n, θ j)‖ ≤ 4 * n / (2 : ℝ) ^ p := by
  rw [← prod_unitPhase]
  have h := product_error_linear (fun j => quantizeComplex p (unitPhase (θ j)))
    (fun j => unitPhase (θ j)) (2 / (2 : ℝ) ^ p) (by positivity) n hn
    (fun j _ => norm_unitPhase (θ j)) (fun j _ => quantizeComplex_error p _)
  convert h using 1
  ring

theorem unitPhase_lipschitz (s t : ℝ) : ‖unitPhase s - unitPhase t‖ ≤ |s - t| := by
  have hid : unitPhase s - unitPhase t =
      (unitPhase (s - t) - 1) * unitPhase t := by
    simp only [unitPhase, sub_mul, one_mul, ← Complex.exp_add, Complex.ofReal_sub]
    congr 2
    ring
  rw [hid, norm_mul, norm_unitPhase, mul_one]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- The integer quotient used by the phase circuit has certified real error. -/
theorem quotient_error {x d q s M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (hq : M * x = d * q + s) (hs : s < d) :
    |(x : ℝ) / d - (q : ℝ) / M| < 1 / (M : ℝ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hqr : (M : ℝ) * x = (d : ℝ) * q + s := by exact_mod_cast hq
  have hsr : (s : ℝ) < d := by exact_mod_cast hs
  have hid : (x : ℝ) / d - (q : ℝ) / M = (s : ℝ) / (d * M) := by
    field_simp
    nlinarith
  rw [hid, abs_of_nonneg (by positivity)]
  apply (div_lt_div_iff₀ (mul_pos hdr hMr) hMr).2
  nlinarith

theorem quotient_phase_error {x d q s M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (hq : M * x = d * q + s) (hs : s < d) :
    ‖unitPhase (2 * Real.pi * ((x : ℝ) / d)) -
      unitPhase (2 * Real.pi * ((q : ℝ) / M))‖ < 2 * Real.pi / M := by
  calc
    _ ≤ |2 * Real.pi * ((x : ℝ) / d) - 2 * Real.pi * ((q : ℝ) / M)| :=
      unitPhase_lipschitz _ _
    _ = (2 * Real.pi) * |(x : ℝ) / d - (q : ℝ) / M| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    _ < (2 * Real.pi) * (1 / (M : ℝ)) :=
      mul_lt_mul_of_pos_left (quotient_error hd hM hq hs) (by positivity)
    _ = _ := by ring

/-- Final rounding is exact once a strict half-integer error is certified. -/
theorem floor_add_half_eq (v : ℝ) (z : ℤ) (h : |v - (z : ℝ)| < 1 / 2) :
    ⌊v + 1 / 2⌋ = z := by
  apply Int.floor_eq_iff.2
  obtain ⟨hl, hu⟩ := abs_lt.1 h
  constructor <;> linarith

end PrimeAlgorithm.PhaseApproximation
