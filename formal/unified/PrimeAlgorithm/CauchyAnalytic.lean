import PrimeAlgorithm.CauchyQuadrature
import PrimeAlgorithm.CauchyLogDomain
import PrimeAlgorithm.CauchyPhase

/-! Uniform Cauchy quadrature for actual holomorphic functions. This connects
the checked finite root filter and series bound to Mathlib's Cauchy formula. -/
noncomputable section
namespace PrimeAlgorithm.Cauchy
open Finset
open scoped Interval

def outerRadius : NNReal := ⟨7 / 8, by norm_num⟩

def circleMeanNorm (f : ℂ → ℂ) (c : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap c (7 / 8) θ)‖

def analyticCoeff (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  (3 / 4 : ℂ) ^ n * (cauchyPowerSeries f c (7 / 8) n (fun _ => 1))

theorem circleMeanNorm_le {f : ℂ → ℂ} {c : ℂ}
    (hf : ContinuousOn f (Metric.closedBall c (7 / 8))) {H : ℝ}
    (hbound : ∀ z ∈ Metric.closedBall c (7 / 8), ‖f z‖ ≤ H) :
    circleMeanNorm f c ≤ H := by
  have hmem (θ : ℝ) : circleMap c (7 / 8) θ ∈ Metric.closedBall c (7 / 8) :=
    Metric.sphere_subset_closedBall (circleMap_mem_sphere c (by norm_num) θ)
  have hcont : Continuous (fun θ : ℝ => ‖f (circleMap c (7 / 8) θ)‖) :=
    (hf.comp_continuous (continuous_circleMap _ _) hmem).norm
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    Real.two_pi_pos.le (hcont.intervalIntegrable 0 (2 * Real.pi))
    (continuous_const.intervalIntegrable 0 (2 * Real.pi))
    (fun θ _ => hbound _ (hmem θ))
  unfold circleMeanNorm
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ∫ _θ : ℝ in 0..2 * Real.pi, H := by
      exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = H := by simp; field_simp

theorem multilinear_diag {n : ℕ} (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => ℂ) ℂ)
    (z : ℂ) : p (fun _ => z) = z ^ n * p (fun _ => 1) := by
  simpa using p.map_smul_univ (fun _ => z) (fun _ => (1 : ℂ))

theorem analyticCoeff_norm_le (f : ℂ → ℂ) (c : ℂ) {H : ℝ}
    (hH : circleMeanNorm f c ≤ H) (n : ℕ) :
    ‖analyticCoeff f c n‖ ≤ H * (6 / 7 : ℝ) ^ n := by
  have hc : ‖cauchyPowerSeries f c (7 / 8) n (fun _ => 1)‖ ≤
      circleMeanNorm f c * (8 / 7 : ℝ) ^ n := by
    calc
      _ ≤ ‖cauchyPowerSeries f c (7 / 8) n‖ := by
        simpa using (cauchyPowerSeries f c (7 / 8) n).le_opNorm (fun _ => 1)
      _ ≤ _ := by
        have h := norm_cauchyPowerSeries_le f c (7 / 8) n
        have heq : |(7 / 8 : ℝ)|⁻¹ = 8 / 7 := by norm_num
        rw [heq] at h
        exact h
  unfold analyticCoeff
  rw [norm_mul, norm_pow]
  norm_num 
  calc
    (3 / 4 : ℝ) ^ n * ‖cauchyPowerSeries f c (7 / 8) n (fun _ => 1)‖ ≤
        (3 / 4 : ℝ) ^ n * (H * (8 / 7 : ℝ) ^ n) := by
      gcongr
      exact hc.trans (mul_le_mul_of_nonneg_right hH (by positivity))
    _ = H * (6 / 7 : ℝ) ^ n := by
      rw [mul_left_comm, ← mul_pow]
      norm_num

theorem analytic_series_eq {f : ℂ → ℂ} {c : ℂ}
    (hf : DifferentiableOn ℂ f (Metric.closedBall c (7 / 8)))
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    seriesEval (analyticCoeff f c) w = f (c + (3 / 4 : ℂ) * w) := by
  have hR : (0 : NNReal) < outerRadius := by change (0 : ℝ) < 7 / 8; norm_num
  have hF := (show DifferentiableOn ℂ f (Metric.closedBall c (outerRadius : ℝ)) from hf).hasFPowerSeriesOnBall hR
  have hw' : (3 / 4 : ℂ) * w ∈ Metric.eball 0 (outerRadius : ENNReal) := by
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, enorm_lt_coe]
    change ‖(3 / 4 : ℂ) * w‖ < (7 / 8 : ℝ)
    rw [norm_mul]
    norm_num
    linarith
  have hs := hF.hasSum hw'
  have heq (n : ℕ) : cauchyPowerSeries f c (outerRadius : ℝ) n
      (fun _ => (3 / 4 : ℂ) * w) = analyticCoeff f c n * w ^ n := by
    change cauchyPowerSeries f c (7 / 8) n (fun _ => (3 / 4 : ℂ) * w) = _
    rw [multilinear_diag, mul_pow]
    simp only [analyticCoeff]
    ring
  simp_rw [heq] at hs
  exact hs.tsum_eq

theorem quadrature_congr {M : ℕ} {ζ q : ℂ} {f g : ℂ → ℂ}
    (h : ∀ j ∈ range M, f (ζ ^ j) = g (ζ ^ j)) :
    quadrature M ζ q f = quadrature M ζ q g := by
  unfold quadrature
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [h j hj]

theorem analytic_quadrature_error {M : ℕ} (hM : 0 < M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ M) {f : ℂ → ℂ} {c q : ℂ}
    (hf : DifferentiableOn ℂ f (Metric.closedBall c (7 / 8)))
    (hq : ‖q‖ ≤ (2 / 3 : ℝ)) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : circleMeanNorm f c ≤ H) :
    ‖quadrature M ζ q (fun w => f (c + (3 / 4 : ℂ) * w)) -
      f (c + (3 / 4 : ℂ) * q)‖ ≤
      (H * (6 / 7 : ℝ) ^ M / (1 - 6 / 7)) / (1 - 2 / 3) +
      (H / (1 - 6 / 7)) * (2 / 3 : ℝ) ^ M / (1 - (2 / 3 : ℝ) ^ M) +
      H * (6 / 7 : ℝ) ^ M / (1 - 6 / 7) := by
  have hn : quadrature M ζ q (fun w => f (c + (3 / 4 : ℂ) * w)) =
      quadrature M ζ q (seriesEval (analyticCoeff f c)) := by
    apply quadrature_congr
    intro j hj
    exact (analytic_series_eq hf (by simp [hζ.norm'_eq_one hM.ne'])).symm
  rw [hn, ← analytic_series_eq hf (hq.trans (by norm_num))]
  exact quadrature_series_error hM hζ (by norm_num) (by norm_num) hq hH0
    (by norm_num) (by norm_num) _ (analyticCoeff_norm_le f c hH)

theorem geometric_error_simplify {M : ℕ} (hM : 0 < M) {H : ℝ} (hH : 0 ≤ H) :
    (H * (6 / 7 : ℝ) ^ M / (1 - 6 / 7)) / (1 - 2 / 3) +
      (H / (1 - 6 / 7)) * (2 / 3 : ℝ) ^ M / (1 - (2 / 3 : ℝ) ^ M) +
      H * (6 / 7 : ℝ) ^ M / (1 - 6 / 7) ≤ 49 * H * (6 / 7 : ℝ) ^ M := by
  have hbeta : (2 / 3 : ℝ) ^ M ≤ 2 / 3 :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hM : (2 / 3 : ℝ) ^ M ≤ (2 / 3 : ℝ) ^ 1) |>.trans_eq (pow_one _)
  have hcomp : (2 / 3 : ℝ) ^ M ≤ (6 / 7 : ℝ) ^ M :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) M
  have hden : (1 / 3 : ℝ) ≤ 1 - (2 / 3 : ℝ) ^ M := by linarith
  have hterm : (H / (1 - 6 / 7)) * (2 / 3 : ℝ) ^ M / (1 - (2 / 3 : ℝ) ^ M) ≤
      21 * H * (6 / 7 : ℝ) ^ M := by
    calc
      _ ≤ (H / (1 - 6 / 7)) * (6 / 7 : ℝ) ^ M / (1 / 3) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left hcomp (by positivity)) (by norm_num) hden
      _ = _ := by ring
  norm_num at hterm ⊢
  linarith

def cauchyApprox (M : ℕ) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  quadrature M (Complex.exp (2 * Real.pi * Complex.I / M)) ((y - center) / (3 / 4))
    (fun w => f (center + (3 / 4) * w))

/-- Actual equispaced Cauchy approximation, uniformly on the whole interval.
Every hypothesis is a directly checkable holomorphic-domain or function bound. -/
theorem cauchyApprox_error {M : ℕ} (hM : 0 < M) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall center (7 / 8))) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ z ∈ Metric.closedBall center (7 / 8), ‖f z‖ ≤ H)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖cauchyApprox M f y - f y‖ ≤ 49 * H * (6 / 7 : ℝ) ^ M := by
  have hq : ‖((y : ℂ) - center) / (3 / 4)‖ ≤ (2 / 3 : ℝ) := by
    rw [norm_div]
    have hi := interval_distance hy
    norm_num
    linarith
  have heq : center + (3 / 4 : ℂ) * (((y : ℂ) - center) / (3 / 4)) = y := by
    field_simp
    ring
  have h := analytic_quadrature_error hM (Complex.isPrimitiveRoot_exp M hM.ne')
    hf.differentiableOn hq hH (circleMeanNorm_le hf.continuousOn hbound)
  rw [heq] at h
  exact h.trans (geometric_error_simplify hM hH)

theorem cauchyApprox_log_error {M : ℕ} (hM : 0 < M) (j : ℕ)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖cauchyApprox M (logAmplitude j) y - logAmplitude j y‖ ≤
      49 * ((j : ℝ) + 6) * (6 / 7 : ℝ) ^ M := by
  apply cauchyApprox_error hM (logAmplitude_analyticOnNhd j) (by positivity) ?_ hy
  intro z hz
  exact logAmplitude_norm_le j (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

theorem cauchyApprox_invLog_error {M j : ℕ} (hM : 0 < M) (hj : 1 ≤ j)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖cauchyApprox M (invLogAmplitude j) y - invLogAmplitude j y‖ ≤
      49 * (Real.log (5 / 4))⁻¹ * (6 / 7 : ℝ) ^ M := by
  apply cauchyApprox_error hM (invLogAmplitude_analyticOnNhd hj)
    (inv_nonneg.mpr (Real.log_nonneg (by norm_num))) ?_ hy
  intro z hz
  exact invLogAmplitude_norm_le hj (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

theorem cauchyApprox_phase_error {M : ℕ} (hM : 0 < M)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖cauchyApprox M shiftedPhase y - shiftedPhase y‖ ≤
      49 * Real.exp (7 * Real.pi / 4) * (6 / 7 : ℝ) ^ M := by
  apply cauchyApprox_error hM (fun z _ => shiftedPhase_analytic z)
    (Real.exp_pos _).le ?_ hy
  intro z hz
  exact shiftedPhase_bound (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

theorem fivefold_geometric_decay (p : ℕ) :
    (6 / 7 : ℝ) ^ (5 * p) ≤ (1 / 2 : ℝ) ^ p := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by norm_num) p

theorem cauchyApprox_precision {p : ℕ} (hp : 0 < p) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall center (7 / 8))) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ z ∈ Metric.closedBall center (7 / 8), ‖f z‖ ≤ H)
    {y : ℝ} (hy : y ∈ Set.Icc 1 2) :
    ‖cauchyApprox (5 * p) f y - f y‖ ≤ 49 * H * (1 / 2 : ℝ) ^ p := by
  exact (cauchyApprox_error (by omega) hf hH hbound hy).trans
    (mul_le_mul_of_nonneg_left (fivefold_geometric_decay p) (by positivity))

end PrimeAlgorithm.Cauchy
