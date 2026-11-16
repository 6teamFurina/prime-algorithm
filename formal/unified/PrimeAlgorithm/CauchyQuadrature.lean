import PrimeAlgorithm.CauchyKernel

/-! Exact Cauchy quadrature on roots of unity. The polynomial identity here is
the algebraic component of the exponentially convergent quadrature proof. -/
noncomputable section
namespace PrimeAlgorithm.Cauchy
open Finset

theorem root_filter {M : ℕ} (hM : 0 < M) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M)
    {a t : ℕ} (ha : a < M) (ht : t < M) :
    (∑ j ∈ range M, (ζ ^ j) ^ a / (ζ ^ j) ^ t) =
      if a = t then (M : ℂ) else 0 := by
  have hz : ζ ≠ 0 := (hζ.isUnit hM.ne').ne_zero
  have hexp (j : ℕ) : (ζ ^ j) ^ a / (ζ ^ j) ^ t = (ζ ^ a / ζ ^ t) ^ j := by
    rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm j a, Nat.mul_comm j t, pow_mul, pow_mul]
  simp_rw [hexp]
  by_cases hat : a = t
  · subst t
    simp [hz]
  · rw [if_neg hat]
    have hne : ζ ^ a / ζ ^ t ≠ 1 := by
      intro he
      have hp : ζ ^ a = ζ ^ t := (div_eq_one_iff_eq (pow_ne_zero _ hz)).mp he
      exact hat (hζ.pow_inj ha ht hp)
    have hp : (ζ ^ a / ζ ^ t) ^ M = 1 := by
      rw [div_pow, ← pow_mul, Nat.mul_comm a M, pow_mul, hζ.pow_eq_one, one_pow,
        ← pow_mul, Nat.mul_comm t M, pow_mul, hζ.pow_eq_one, one_pow, div_one]
    have hg := geom_sum_mul_neg (ζ ^ a / ζ ^ t) M
    rw [hp, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne.symm)

theorem cauchy_kernel_geom {M : ℕ} {w q : ℂ} (hw : w ^ M = 1)
    (hM : 0 < M) (hq : q ^ M ≠ 1) :
    w / (w - q) = (∑ t ∈ range M, (q / w) ^ t) / (1 - q ^ M) := by
  have hw0 : w ≠ 0 := by intro he; simp [he, hM.ne'] at hw
  have hwq : w - q ≠ 0 := by
    intro he
    have heq := sub_eq_zero.mp he
    exact hq (heq ▸ hw)
  have hden : 1 - q ^ M ≠ 0 := sub_ne_zero.mpr hq.symm
  have hg := geom_sum_mul_neg (q / w) M
  rw [div_pow, hw, div_one] at hg
  have hratio : 1 - q / w = (w - q) / w := by field_simp
  rw [hratio] at hg
  apply (eq_div_iff hden).mpr
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hwq).mpr
  calc
    w * (1 - q ^ M) = w * ((∑ t ∈ range M, (q / w) ^ t) * ((w - q) / w)) := by rw [hg]
    _ = (∑ t ∈ range M, (q / w) ^ t) * (w - q) := by field_simp

theorem cauchy_monomial {M : ℕ} (hM : 0 < M) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M)
    {a : ℕ} (ha : a < M) {q : ℂ} (hq : q ^ M ≠ 1) :
    (∑ j ∈ range M, (ζ ^ j) ^ a * (ζ ^ j / (ζ ^ j - q))) =
      (M : ℂ) * q ^ a / (1 - q ^ M) := by
  have hpow (j : ℕ) : (ζ ^ j) ^ M = 1 := by
    rw [← pow_mul, Nat.mul_comm j M, pow_mul, hζ.pow_eq_one, one_pow]
  simp_rw [cauchy_kernel_geom (hpow _) hM hq, ← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  calc
    (∑ t ∈ range M, ∑ j ∈ range M, (ζ ^ j) ^ a * (q / ζ ^ j) ^ t) =
        ∑ t ∈ range M, q ^ t * (∑ j ∈ range M, (ζ ^ j) ^ a / (ζ ^ j) ^ t) := by
      apply sum_congr rfl
      intro t ht
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [div_pow]
      ring
    _ = (M : ℂ) * q ^ a := by
      rw [sum_eq_single a]
      · rw [root_filter hM hζ ha ha]
        simp [mul_comm]
      · intro t ht hta
        rw [root_filter hM hζ ha (mem_range.mp ht)]
        simp [Ne.symm hta]
      · intro hnot
        exact False.elim (hnot (mem_range.mpr ha))

def quadrature (M : ℕ) (ζ q : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∑ j ∈ range M, f (ζ ^ j) * (ζ ^ j / (ζ ^ j - q))) / M

def polyEval (M : ℕ) (c : ℕ → ℂ) (q : ℂ) : ℂ :=
  ∑ a ∈ range M, c a * q ^ a

theorem quadrature_polynomial {M : ℕ} (hM : 0 < M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ M) {q : ℂ} (hq : q ^ M ≠ 1) (c : ℕ → ℂ) :
    quadrature M ζ q (polyEval M c) = polyEval M c q / (1 - q ^ M) := by
  have hsum : (∑ j ∈ range M, polyEval M c (ζ ^ j) * (ζ ^ j / (ζ ^ j - q))) =
      (M : ℂ) * polyEval M c q / (1 - q ^ M) := by
    unfold polyEval
    simp_rw [sum_mul]
    rw [sum_comm]
    calc
      (∑ a ∈ range M, ∑ j ∈ range M, c a * (ζ ^ j) ^ a * (ζ ^ j / (ζ ^ j - q))) =
          ∑ a ∈ range M, c a * ((M : ℂ) * q ^ a / (1 - q ^ M)) := by
        apply sum_congr rfl
        intro a ha
        rw [← cauchy_monomial hM hζ (mem_range.mp ha) hq, mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
      _ = (M : ℂ) * (∑ a ∈ range M, c a * q ^ a) / (1 - q ^ M) := by
        rw [mul_sum, sum_div]
        apply sum_congr rfl
        intro a ha
        ring
  unfold quadrature
  rw [hsum]
  have hm0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

/-- A pointwise coefficient bound gives an actual convergent Taylor series and
a uniform tail bound; the error estimate is proved, not assumed. -/
theorem series_tail_bound {c : ℕ → ℂ} {H ρ : ℝ}
    (hH : 0 ≤ H) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc : ∀ n, ‖c n‖ ≤ H * ρ ^ n) (M : ℕ) :
    Summable c ∧ ‖(∑' n, c n) - ∑ n ∈ range M, c n‖ ≤ H * ρ ^ M / (1 - ρ) := by
  have hg := hasSum_geometric_of_lt_one hρ hρ1
  have hsum : Summable c := (hg.summable.mul_left H).of_norm_bounded hc
  refine ⟨hsum, ?_⟩
  have ht : ‖∑' n, c (n + M)‖ ≤ H * ρ ^ M / (1 - ρ) := by
    have hb : HasSum (fun n : ℕ => (H * ρ ^ M) * ρ ^ n)
        (H * ρ ^ M / (1 - ρ)) := by
      simpa [div_eq_mul_inv] using hg.mul_left (H * ρ ^ M)
    apply tsum_of_norm_bounded hb
    intro n
    calc ‖c (n + M)‖ ≤ H * ρ ^ (n + M) := hc _
      _ = H * ρ ^ M * ρ ^ n := by rw [pow_add]; ring
  have heq := hsum.sum_add_tsum_nat_add M
  rw [← heq]
  simpa using ht

theorem quadrature_sub (M : ℕ) (ζ q : ℂ) (f g : ℂ → ℂ) :
    quadrature M ζ q f - quadrature M ζ q g =
      quadrature M ζ q (fun z => f z - g z) := by
  simp [quadrature, sub_mul, sum_sub_distrib, sub_div]

theorem kernel_norm_le {w q : ℂ} {r : ℝ} (hw : ‖w‖ = 1)
    (hq : ‖q‖ ≤ r) (hr : r < 1) : ‖w / (w - q)‖ ≤ 1 / (1 - r) := by
  have hd : 1 - r ≤ ‖w - q‖ := by
    have h := norm_sub_norm_le w q
    rw [hw] at h
    linarith
  rw [norm_div, hw]
  exact one_div_le_one_div_of_le (sub_pos.mpr hr) hd

theorem quadrature_norm_le {M : ℕ} (hM : 0 < M) {ζ q : ℂ}
    (hζ : ‖ζ‖ = 1) {r E : ℝ} (hq : ‖q‖ ≤ r) (hr : r < 1) (hE : 0 ≤ E)
    (f : ℂ → ℂ) (hf : ∀ j ∈ range M, ‖f (ζ ^ j)‖ ≤ E) :
    ‖quadrature M ζ q f‖ ≤ E / (1 - r) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum : ‖∑ j ∈ range M, f (ζ ^ j) * (ζ ^ j / (ζ ^ j - q))‖ ≤
      (M : ℝ) * (E / (1 - r)) := by
    calc
      _ ≤ ∑ j ∈ range M, E / (1 - r) := by
        apply norm_sum_le_of_le
        intro j hj
        rw [norm_mul]
        calc
          ‖f (ζ ^ j)‖ * ‖ζ ^ j / (ζ ^ j - q)‖ ≤ E * (1 / (1 - r)) :=
            mul_le_mul (hf j hj) (kernel_norm_le (by simp [hζ]) hq hr)
              (norm_nonneg _) hE
          _ = E / (1 - r) := by ring
      _ = _ := by simp
  unfold quadrature
  rw [norm_div]
  simp only [Complex.norm_natCast]
  exact (div_le_iff₀ hm).mpr (by simpa [mul_comm] using hsum)

theorem power_ne_one {M : ℕ} (hM : 0 < M) {q : ℂ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hq : ‖q‖ ≤ r) : q ^ M ≠ 1 := by
  have h : ‖q ^ M‖ < 1 := by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hq M).trans_lt (pow_lt_one₀ hr0 hr1 hM.ne')
  intro he
  simp [he] at h

theorem polynomial_alias_error {M : ℕ} (hM : 0 < M) {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ M) {r B : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq : ‖q‖ ≤ r) (hB : 0 ≤ B) (c : ℕ → ℂ) (hc : ‖polyEval M c q‖ ≤ B) :
    ‖quadrature M ζ q (polyEval M c) - polyEval M c q‖ ≤
      B * r ^ M / (1 - r ^ M) := by
  have hp := power_ne_one hM hr0 hr1 hq
  have hd : (1 : ℂ) - q ^ M ≠ 0 := sub_ne_zero.mpr hp.symm
  rw [quadrature_polynomial hM hζ hp]
  have heq : polyEval M c q / (1 - q ^ M) - polyEval M c q =
      polyEval M c q * q ^ M / (1 - q ^ M) := by field_simp; ring
  rw [heq, norm_div, norm_mul, norm_pow]
  have hrpow : r ^ M < 1 := pow_lt_one₀ hr0 hr1 hM.ne'
  have hqp : ‖q‖ ^ M ≤ r ^ M := pow_le_pow_left₀ (norm_nonneg _) hq M
  have hden : 1 - r ^ M ≤ ‖(1 : ℂ) - q ^ M‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (q ^ M)
    rw [norm_one, norm_pow] at h
    linarith
  apply div_le_div₀ (mul_nonneg hB (pow_nonneg hr0 _))
    (mul_le_mul hc hqp (pow_nonneg (norm_nonneg _) _) hB) (sub_pos.mpr hrpow) hden

theorem quadrature_error_of_polynomial {M : ℕ} (hM : 0 < M) {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ M) {r E F B : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq : ‖q‖ ≤ r) (hE : 0 ≤ E) (hB : 0 ≤ B) (c : ℕ → ℂ) (f : ℂ → ℂ)
    (hnodes : ∀ j ∈ range M, ‖f (ζ ^ j) - polyEval M c (ζ ^ j)‖ ≤ E)
    (hpoint : ‖polyEval M c q - f q‖ ≤ F) (hpoly : ‖polyEval M c q‖ ≤ B) :
    ‖quadrature M ζ q f - f q‖ ≤ E / (1 - r) + B * r ^ M / (1 - r ^ M) + F := by
  have h1 : ‖quadrature M ζ q f - quadrature M ζ q (polyEval M c)‖ ≤ E / (1 - r) := by
    rw [quadrature_sub]
    exact quadrature_norm_le hM (hζ.norm'_eq_one hM.ne') hq hr1 hE _ hnodes
  have h2 := polynomial_alias_error hM hζ hr0 hr1 hq hB c hpoly
  have h3 := norm_sub_le_norm_sub_add_norm_sub (quadrature M ζ q f)
    (quadrature M ζ q (polyEval M c)) (f q)
  have h4 := norm_sub_le_norm_sub_add_norm_sub (quadrature M ζ q (polyEval M c))
    (polyEval M c q) (f q)
  linarith

def seriesEval (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, c n * z ^ n

theorem series_poly_error {c : ℕ → ℂ} {H ρ : ℝ}
    (hH : 0 ≤ H) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc : ∀ n, ‖c n‖ ≤ H * ρ ^ n) (M : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖seriesEval c z - polyEval M c z‖ ≤ H * ρ ^ M / (1 - ρ) := by
  apply (series_tail_bound hH hρ hρ1 (c := fun n => c n * z ^ n) ?_ M).2
  intro n
  rw [norm_mul, norm_pow]
  exact (mul_le_mul (hc n) (pow_le_one₀ (norm_nonneg _) hz)
    (pow_nonneg (norm_nonneg _) _) (mul_nonneg hH (pow_nonneg hρ _))).trans_eq (mul_one _)

theorem poly_norm_le {c : ℕ → ℂ} {H ρ : ℝ}
    (hH : 0 ≤ H) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc : ∀ n, ‖c n‖ ≤ H * ρ ^ n) (M : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖polyEval M c z‖ ≤ H / (1 - ρ) := by
  have hgeo := (hasSum_geometric_of_lt_one hρ hρ1).mul_left H
  calc
    ‖polyEval M c z‖ ≤ ∑ n ∈ range M, H * ρ ^ n := by
      apply norm_sum_le_of_le
      intro n hn
      rw [norm_mul, norm_pow]
      exact (mul_le_mul (hc n) (pow_le_one₀ (norm_nonneg _) hz)
        (pow_nonneg (norm_nonneg _) _) (mul_nonneg hH (pow_nonneg hρ _))).trans_eq (mul_one _)
    _ ≤ ∑' n, H * ρ ^ n :=
      hgeo.summable.sum_le_tsum (range M) (fun n _ => mul_nonneg hH (pow_nonneg hρ n))
    _ = H / (1 - ρ) := by rw [hgeo.tsum_eq]; rfl

/-- Uniform exponentially decaying error for the actual M-node quadrature of
an analytic power series. This proves the error from coefficient bounds. -/
theorem quadrature_series_error {M : ℕ} (hM : 0 < M) {ζ q : ℂ}
    (hζ : IsPrimitiveRoot ζ M) {r H ρ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hq : ‖q‖ ≤ r) (hH : 0 ≤ H) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ H * ρ ^ n) :
    ‖quadrature M ζ q (seriesEval c) - seriesEval c q‖ ≤
      (H * ρ ^ M / (1 - ρ)) / (1 - r) +
      (H / (1 - ρ)) * r ^ M / (1 - r ^ M) + H * ρ ^ M / (1 - ρ) := by
  apply quadrature_error_of_polynomial hM hζ hr0 hr1 hq
    (by positivity) (by positivity) c (seriesEval c)
  · intro j hj
    exact series_poly_error hH hρ hρ1 hc M (by simp [hζ.norm'_eq_one hM.ne'])
  · rw [norm_sub_rev]
    exact series_poly_error hH hρ hρ1 hc M (hq.trans hr1.le)
  · exact poly_norm_le hH hρ hρ1 hc M (hq.trans hr1.le)

end PrimeAlgorithm.Cauchy
