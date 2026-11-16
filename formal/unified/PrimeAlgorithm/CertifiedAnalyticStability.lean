import PrimeAlgorithm.CauchyPrecision
import Mathlib.Analysis.Calculus.MeanValue

/-! Local stability for the effective coefficient generator. -/
namespace PrimeAlgorithm.CertifiedAnalyticStability
open PrimeAlgorithm.Cauchy

theorem log_lipschitz {z w : ℂ}
    (hz : ‖z-center‖ ≤ (7/8:ℝ)) (hw : ‖w-center‖ ≤ (7/8:ℝ)) :
    ‖Complex.log z-Complex.log w‖ ≤ 2*‖z-w‖ := by
  let s := Metric.closedBall center (7/8:ℝ)
  have hs : Convex ℝ s := convex_closedBall _ _
  have hd : ∀x∈s, HasDerivWithinAt Complex.log x⁻¹ s x := by
    intro x hx
    have hx' : ‖x-center‖ ≤ (7/8:ℝ) := by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hx
    exact (Complex.hasDerivAt_log (disk_slitPlane hx')).hasDerivWithinAt
  have hb : ∀x∈s, ‖x⁻¹‖ ≤ (2:ℝ) := by
    intro x hx
    have hx' : ‖x-center‖ ≤ (7/8:ℝ) := by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hx
    have h := inv_anti₀ (by norm_num : (0:ℝ)<5/8) (disk_norm_lower hx')
    rw [norm_inv]
    norm_num at h
    linarith
  exact hs.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hw)
    (by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz)

theorem logAmplitude_lipschitz (j : ℕ) {z w : ℂ}
    (hz : ‖z-center‖ ≤ (7/8:ℝ)) (hw : ‖w-center‖ ≤ (7/8:ℝ)) :
    ‖logAmplitude j z-logAmplitude j w‖ ≤ 2*‖z-w‖ := by
  simpa only [logAmplitude, add_sub_add_left_eq_sub] using log_lipschitz hz hw

theorem logAmplitude_norm_lower {j : ℕ} (hj : 1≤j) {z : ℂ}
    (hz : ‖z-center‖ ≤ (7/8:ℝ)) : (1/5:ℝ) ≤ ‖logAmplitude j z‖ := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<5/4)
  have hl : (1/5:ℝ) ≤ Real.log (5/4) := by norm_num at h; exact h
  exact hl.trans ((logAmplitude_re_lower hj hz).trans
    ((le_abs_self _).trans (Complex.abs_re_le_norm _)))

theorem inverse_perturbation {v q : ℂ}
    (hv : (1/5:ℝ) ≤ ‖v‖) (he : ‖q-v‖ ≤ (1/10:ℝ)) :
    (1/10:ℝ) ≤ ‖q‖ ∧ ‖q⁻¹-v⁻¹‖ ≤ 50*‖q-v‖ := by
  have hq : (1/10:ℝ) ≤ ‖q‖ := by
    have h := norm_le_norm_sub_add v q
    rw [norm_sub_rev v q] at h
    linarith
  refine ⟨hq,?_⟩
  have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
  have hq0 : q ≠ 0 := by intro h; norm_num [h] at hq
  have hid : q⁻¹-v⁻¹ = (v-q)/(q*v) := by field_simp
  rw [hid, norm_div, norm_mul, norm_sub_rev v q]
  have hp : (1/50:ℝ) ≤ ‖q‖*‖v‖ := by nlinarith
  have h := div_le_div_of_nonneg_left (norm_nonneg (q-v)) (by norm_num : (0:ℝ)<1/50) hp
  norm_num at h
  nlinarith

theorem invLog_perturbation {j : ℕ} (hj : 1≤j) {z q : ℂ}
    (hz : ‖z-center‖ ≤ (7/8:ℝ))
    (he : ‖q-logAmplitude j z‖ ≤ (1/10:ℝ)) :
    (1/10:ℝ) ≤ ‖q‖ ∧ ‖q⁻¹-invLogAmplitude j z‖ ≤ 50*‖q-logAmplitude j z‖ :=
  inverse_perturbation (logAmplitude_norm_lower hj hz) he

end PrimeAlgorithm.CertifiedAnalyticStability
