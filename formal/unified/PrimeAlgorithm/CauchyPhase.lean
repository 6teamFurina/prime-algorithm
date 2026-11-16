import PrimeAlgorithm.CauchyKernel
import PrimeAlgorithm.RamanujanSum

/-! The second implementation of the phase uses the same rational Cauchy
kernel as the logarithms. Its input is shifted to the common interval [1,2]. -/

noncomputable section

namespace PrimeAlgorithm.Cauchy

def shiftedPhase (z : ℂ) : ℂ :=
  Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (z - 1))

theorem shiftedPhase_analytic (z : ℂ) : AnalyticAt ℂ shiftedPhase z := by
  unfold shiftedPhase
  fun_prop

theorem shiftedPhase_bound {z : ℂ} (hz : ‖z - center‖ ≤ (7 / 8 : ℝ)) :
    ‖shiftedPhase z‖ ≤ Real.exp (7 * Real.pi / 4) := by
  have hi : |z.im| ≤ (7 / 8 : ℝ) := by
    have h := Complex.abs_im_le_norm (z - center)
    simpa [center] using h.trans hz
  have hlo := (abs_le.1 hi).1
  unfold shiftedPhase
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  norm_num
  have hp := Real.pi_pos
  nlinarith

theorem shiftedPhase_ratio (d x : ℕ) :
    shiftedPhase (1 + (x : ℂ) / d) = Ramanujan.phase d x := by
  unfold shiftedPhase Ramanujan.phase
  congr 1
  ring

theorem shifted_ratio_interval {d x : ℕ} (hd : 0 < d) (hx : x < d) :
    1 + (x : ℝ) / d ∈ Set.Icc (1 : ℝ) 2 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hxr : (x : ℝ) < d := by exact_mod_cast hx
  constructor
  · have : 0 ≤ (x : ℝ) / d := by positivity
    linarith
  · have : (x : ℝ) / d < 1 := (div_lt_one hdr).2 hxr
    linarith

end PrimeAlgorithm.Cauchy
