import PrimeAlgorithm.CauchyKernel

/-! The actual logarithm and reciprocal logarithm are analytic on the complete
closed outer Cauchy disk. The denominator has a uniform positive lower bound. -/

noncomputable section
namespace PrimeAlgorithm.Cauchy

def logAmplitude (j : ℕ) (z : ℂ) : ℂ :=
  (j : ℂ) * (Real.log 2 : ℂ) + Complex.log z

def invLogAmplitude (j : ℕ) (z : ℂ) : ℂ := (logAmplitude j z)⁻¹

theorem disk_re_lower {z : ℂ} (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) :
    (5 / 8 : ℝ) ≤ z.re := by
  have h := (Complex.abs_re_le_norm (z - center)).trans hz
  have h' := (abs_le.mp h).1
  simp only [Complex.sub_re, center, Complex.ofReal_re] at h'
  linarith

theorem disk_slitPlane {z : ℂ} (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) :
    z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le (by norm_num) (disk_re_lower hz)))

theorem disk_norm_lower {z : ℂ} (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) :
    (5 / 8 : ℝ) ≤ ‖z‖ :=
  (disk_re_lower hz).trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))

theorem logAmplitude_re_lower {j : ℕ} (hj : 1 ≤ j) {z : ℂ}
    (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) :
    Real.log (5 / 4) ≤ (logAmplitude j z).re := by
  have hnorm := disk_norm_lower hz
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 5 / 8) hnorm
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have htwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hm : Real.log 2 ≤ (j : ℝ) * Real.log 2 := by nlinarith
  have hprod : Real.log (5 / 4) = Real.log 2 + Real.log (5 / 8) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 / 8 : ℝ) ≠ 0)]
    norm_num
  simp only [logAmplitude, Complex.add_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.log_re]
  linarith

theorem logAmplitude_ne_zero {j : ℕ} (hj : 1 ≤ j) {z : ℂ}
    (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) : logAmplitude j z ≠ 0 := by
  have hpos : 0 < (logAmplitude j z).re :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 5 / 4)).trans_le (logAmplitude_re_lower hj hz)
  intro heq
  simp [heq] at hpos

theorem invLogAmplitude_norm_le {j : ℕ} (hj : 1 ≤ j) {z : ℂ}
    (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) :
    ‖invLogAmplitude j z‖ ≤ (Real.log (5 / 4))⁻¹ := by
  have hpos : (0 : ℝ) < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hbound : Real.log (5 / 4) ≤ ‖logAmplitude j z‖ :=
    (logAmplitude_re_lower hj hz).trans
      ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  simpa [invLogAmplitude, norm_inv] using inv_anti₀ hpos hbound

theorem log_analyticAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ Complex.log z := by
  have hdiff : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
    fun _ hw => (Complex.differentiableAt_log hw).differentiableWithinAt
  exact hdiff.analyticOnNhd Complex.isOpen_slitPlane z hz

theorem logAmplitude_analyticOnNhd (j : ℕ) :
    AnalyticOnNhd ℂ (logAmplitude j) (Metric.closedBall center (7 / 8)) := by
  intro z hz
  have hd : ‖z - center‖ ≤ (7 / 8 : ℝ) := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  exact analyticAt_const.add (log_analyticAt (disk_slitPlane hd))

theorem invLogAmplitude_analyticOnNhd {j : ℕ} (hj : 1 ≤ j) :
    AnalyticOnNhd ℂ (invLogAmplitude j) (Metric.closedBall center (7 / 8)) := by
  intro z hz
  have hd : ‖z - center‖ ≤ (7 / 8 : ℝ) := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  exact (logAmplitude_analyticOnNhd j z hz).inv (logAmplitude_ne_zero hj hd)

theorem disk_norm_upper {z : ℂ} (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) :
    ‖z‖ ≤ (19 / 8 : ℝ) := by
  have h := norm_add_le (z - center) center
  simp only [sub_add_cancel] at h
  have hc : ‖center‖ = (3 / 2 : ℝ) := by norm_num [center]
  rw [hc] at h
  linarith

theorem disk_log_norm_le {z : ℂ} (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) :
    ‖Complex.log z‖ ≤ 6 := by
  have hlo := disk_norm_lower hz
  have hhi := disk_norm_upper hz
  have hp : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hlo
  have hloghi := Real.log_le_sub_one_of_pos hp
  have hloglo := Real.one_sub_inv_le_log_of_pos hp
  have hinv : ‖z‖⁻¹ ≤ (8 / 5 : ℝ) := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 5 / 8) hlo
    norm_num at this
    exact this
  have hlog : |Real.log ‖z‖| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hnorm := Complex.norm_le_abs_re_add_abs_im (Complex.log z)
  rw [Complex.log_re, Complex.log_im] at hnorm
  have harg := Complex.abs_arg_le_pi z
  have hpi := Real.pi_lt_four
  linarith

theorem logAmplitude_norm_le (j : ℕ) {z : ℂ}
    (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) : ‖logAmplitude j z‖ ≤ (j : ℝ) + 6 := by
  have hlog : |Real.log 2| ≤ 1 := by
    rw [abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    ‖logAmplitude j z‖ ≤ ‖(j : ℂ) * (Real.log 2 : ℂ)‖ + ‖Complex.log z‖ := norm_add_le _ _
    _ ≤ (j : ℝ) + 6 := by
      rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
      have := disk_log_norm_le hz
      have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) j)
      linarith

end PrimeAlgorithm.Cauchy
