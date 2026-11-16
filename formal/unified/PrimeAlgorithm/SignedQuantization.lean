import PrimeAlgorithm.PhaseApproximation

/-! Rounding toward zero matches a network that counts the floor of a
nonnegative magnitude and applies its sign externally. -/

noncomputable section
namespace PrimeAlgorithm.SignedQuantization
open PrimeAlgorithm.PhaseApproximation

def truncateReal (p : ℕ) (x : ℝ) : ℝ :=
  if 0 ≤ x then quantizeReal p x else -quantizeReal p (-x)

def truncateComplex (p : ℕ) (z : ℂ) : ℂ :=
  ⟨truncateReal p z.re, truncateReal p z.im⟩

theorem truncateReal_error (p : ℕ) (x : ℝ) :
    |truncateReal p x - x| < 1 / (2 : ℝ) ^ p := by
  unfold truncateReal
  split_ifs with hx
  · exact quantizeReal_error p x
  · have h := quantizeReal_error p (-x)
    rw [show -quantizeReal p (-x) - x = -(quantizeReal p (-x) - (-x)) by ring,
      abs_neg]
    exact h

theorem truncateComplex_error (p : ℕ) (z : ℂ) :
    ‖truncateComplex p z - z‖ ≤ 2 / (2 : ℝ) ^ p := by
  have h := Complex.norm_le_abs_re_add_abs_im (truncateComplex p z - z)
  simp only [truncateComplex, Complex.sub_re, Complex.sub_im] at h
  have h1 := truncateReal_error p z.re
  have h2 := truncateReal_error p z.im
  calc
    _ ≤ |truncateReal p z.re - z.re| + |truncateReal p z.im - z.im| := h
    _ ≤ 1 / (2 : ℝ) ^ p + 1 / (2 : ℝ) ^ p := add_le_add h1.le h2.le
    _ = _ := by ring

theorem truncateReal_magnitude (p : ℕ) (x : ℝ) :
    truncateReal p x = (if 0 ≤ x then (1 : ℝ) else -1) *
      ((⌊(2 : ℝ) ^ p * |x|⌋ : ℤ) / (2 : ℝ) ^ p) := by
  unfold truncateReal quantizeReal
  split_ifs with hx
  · rw [abs_of_nonneg hx]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx)]
    ring

theorem truncateReal_neg (p : ℕ) (x : ℝ) : truncateReal p (-x) = -truncateReal p x := by
  by_cases hx : x = 0
  · subst x
    simp [truncateReal, quantizeReal]
  by_cases hp : 0 < x
  · simp [truncateReal, hp.le, not_le.mpr (neg_neg_of_pos hp)]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [truncateReal, not_le.mpr hn, (neg_pos.mpr hn).le]

end PrimeAlgorithm.SignedQuantization
