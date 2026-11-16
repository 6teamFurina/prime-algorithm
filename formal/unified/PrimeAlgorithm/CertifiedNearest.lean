import PrimeAlgorithm.CertifiedRawTaylor
import PrimeAlgorithm.CertifiedCauchy

set_option maxHeartbeats 1000000

namespace PrimeAlgorithm.CertifiedNearest

open Groundwork ClauseBound.ParityChecks.CertLib CertifiedRawGaussian
  CertifiedGaussianRat CertifiedCauchy

/-- Integer arithmetic for nearest rounding, including negative numerators. -/
def coordinate (p : ℕ) (a : ℤ) (d : ℕ) : ℤ :=
  (((2 * 2 ^ p : ℕ) : ℤ) * a / (d : ℤ) + 1) / 2

def nearest (p : ℕ) (z : Raw) : GaussianIntPair :=
  (coordinate p z.1 z.2.2, coordinate p z.2.1 z.2.2)

theorem coordinate_eq_round (p : ℕ) (a : ℤ) (d : ℕ) :
    coordinate p a d = _root_.round ((2 : ℚ) ^ p * ((a : ℚ) / d)) := by
  rw [round_eq_div]
  have he : (2 : ℚ) * (2 ^ p * ((a : ℚ) / d)) =
      (((((2 * 2 ^ p : ℕ) : ℤ) * a) : ℤ) : ℚ) / d := by push_cast; ring
  rw [he, Rat.floor_intCast_div_natCast]
  rfl

theorem coordinate_error (p : ℕ) (a : ℤ) (d : ℕ) :
    |(coordinate p a d : ℝ) / (2 : ℝ) ^ p - (a : ℝ) / d| ≤
      1 / (2 * (2 : ℝ) ^ p) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have he : (_root_.round ((2 : ℝ) ^ p * ((a : ℝ) / d))) = coordinate p a d := by
    rw [coordinate_eq_round]
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_div,
      Rat.cast_intCast, Rat.cast_natCast] using
      (Rat.round_cast (α := ℝ) ((2 : ℚ) ^ p * ((a : ℚ) / d)))
  have h := abs_sub_round ((2 : ℝ) ^ p * ((a : ℝ) / d))
  rw [he, abs_sub_comm] at h
  have hi : (coordinate p a d : ℝ) / (2 : ℝ) ^ p - (a : ℝ) / d =
      ((coordinate p a d : ℝ) - (2 : ℝ) ^ p * ((a : ℝ) / d)) / 2 ^ p := by
    rw [sub_div, mul_div_cancel_left₀ _ hp.ne']
  rw [hi, abs_div, abs_of_pos hp]
  calc
    _ ≤ (1 / 2 : ℝ) / 2 ^ p := div_le_div_of_nonneg_right h hp.le
    _ = _ := by ring

theorem nearest_error (p : ℕ) (z : Raw) :
    ‖value p (nearest p z) - embed (interpret z)‖ ≤ 1 / (2 : ℝ) ^ p := by
  have hr := coordinate_error p z.1 z.2.2
  have hi := coordinate_error p z.2.1 z.2.2
  have he : (value p (nearest p z) - embed (interpret z)).re =
      (coordinate p z.1 z.2.2 : ℝ) / 2 ^ p - (z.1 : ℝ) / z.2.2 := by
    rw [embed_interpret]
    dsimp only [value, nearest]
    rw [show (2 : ℂ) ^ p = ((2 : ℝ) ^ p : ℝ) by norm_cast]
    simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.div_natCast_re,
      Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hf : (value p (nearest p z) - embed (interpret z)).im =
      (coordinate p z.2.1 z.2.2 : ℝ) / 2 ^ p - (z.2.1 : ℝ) / z.2.2 := by
    rw [embed_interpret]
    dsimp only [value, nearest]
    rw [show (2 : ℂ) ^ p = ((2 : ℝ) ^ p : ℝ) by norm_cast]
    simp only [Complex.sub_im, Complex.div_ofReal_im, Complex.div_natCast_im,
      Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add]
  calc
    _ ≤ |(value p (nearest p z) - embed (interpret z)).re| +
        |(value p (nearest p z) - embed (interpret z)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / (2 * (2 : ℝ) ^ p) + 1 / (2 * (2 : ℝ) ^ p) := by rw [he, hf]; linarith
    _ = _ := by ring

theorem coordinate_polyT {α : Type} [Enc α] {p : α → ℕ} {a : α → ℤ} {d : α → ℕ}
    (hp : Unary p) (ha : PolyT a) (hd : PolyT d) :
    PolyT (fun x => coordinate (p x) (a x) (d x)) := by
  have hpow := PolyT.pow_unary (PolyT.const 2) hp
  have hnum : PolyT (fun x => (((2 * 2 ^ p x : ℕ) : ℤ) * a x)) := by fun_prop
  have hdiv := divZ_polyT hnum hd
  exact divZ_polyT (PolyT.addZ hdiv (PolyT.const 1)) (PolyT.const 2)

theorem nearest_polyT {α : Type} [Enc α] {p : α → ℕ} {z : α → Raw}
    (hp : Unary p) (hz : PolyT z) : PolyT (fun x => nearest (p x) (z x)) :=
  PolyT.prodMk (coordinate_polyT hp hz.fst hz.snd.snd)
    (coordinate_polyT hp hz.snd.fst hz.snd.snd)

end PrimeAlgorithm.CertifiedNearest
