import PrimeAlgorithm.PrimeQueryBounds
import PrimeAlgorithm.CertifiedGeneratorAccuracy

namespace PrimeAlgorithm.PrimeMachineInput
open Groundwork EthFollowup.ModP EthFollowup.Primes

/-- Precision is recovered from the value, so zero padding does not change it. -/
def precision (w : List Bool) : ℕ := (Nat.bits (ofWord w)).length + 1

theorem precision_unary : Unary precision := by
  unfold precision
  fun_prop

theorem precision_le (w : List Bool) : precision w ≤ w.length + 1 := by
  have h := bits_length_le (Groundwork.ofWord_lt w)
  simpa only [precision,Nat.add_le_add_iff_right] using h

theorem value_bound (w : List Bool) : ofWord w ≤ 2 ^ precision w := by
  have h : ofWord w < 2 ^ (Nat.bits (ofWord w)).length := by
    simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self (ofWord w)
  exact h.le.trans (Nat.pow_le_pow_right (by decide) (by unfold precision; omega))

@[simp] theorem precision_pad (w : List Bool) : precision (LinearPadding.pad w)=precision w := by
  simp only [precision,LinearPadding.pad_value]

theorem padded_box_width (w : List Bool) :
    5 * CertifiedCoordinateBounds.inputBits (precision (LinearPadding.pad w)) + 2 ≤
      (LinearPadding.pad w).length := by
  rw [precision_pad]
  exact LinearPadding.box_width_fits (precision_le w)

theorem padded_query_width (w : List Bool) :
    24 * CertifiedCoordinateBounds.inputBits (precision (LinearPadding.pad w)) ≤
      (LinearPadding.pad w).length := by
  rw [precision_pad]
  exact LinearPadding.query_width_fits (precision_le w)

end PrimeAlgorithm.PrimeMachineInput
