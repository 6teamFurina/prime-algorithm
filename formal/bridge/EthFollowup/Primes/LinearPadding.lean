import EthFollowup.ModP.CntPad
import EthFollowup.ModP.EncodeList
import EthFollowup.ModP.SpecSq
import PrimeAlgorithm.CertifiedCoordinateBounds

/-! A fixed linear padding for the full prime-sum reader. It accommodates
both the actual arithmetic box and all 24 encoded query parameters. -/
namespace EthFollowup.Primes.LinearPadding
open Groundwork EthFollowup.ModP

def repeated (k : ℕ) (w : List Bool) : List Bool := (padW 1)^[k] w

theorem repeated_polyT (k : ℕ) : PolyT (repeated k) := by
  induction k with
  | zero =>
    change PolyT (fun w => repeated 0 w)
    simpa [repeated] using (PolyT.id' (α:=List Bool))
  | succ k ih =>
    have h : PolyT (fun w => padW 1 (repeated k w)) := (padW_polyT 1).comp ih
    change PolyT (fun w => repeated (k+1) w)
    simpa [repeated, Function.iterate_succ_apply'] using h

theorem repeated_length (k : ℕ) (w : List Bool) :
    (repeated k w).length+1 = 2^k*(w.length+1) := by
  induction k with
  | zero => simp [repeated]
  | succ k ih =>
    have h : repeated (k+1) w = padW 1 (repeated k w) := by
      simp [repeated, Function.iterate_succ_apply']
    rw [h,length_padW,pow_succ]
    nlinarith

theorem repeated_value (k : ℕ) (w : List Bool) :
    Groundwork.ofWord (repeated k w) = Groundwork.ofWord w := by
  induction k with
  | zero => simp [repeated]
  | succ k ih =>
    simpa [repeated,Function.iterate_succ_apply',gofWord_padW] using ih

def pad (w : List Bool) : List Bool := repeated 11 w

theorem pad_polyT : PolyT pad := repeated_polyT 11

theorem pad_value (w : List Bool) : Groundwork.ofWord (pad w) = Groundwork.ofWord w :=
  repeated_value 11 w

theorem pad_length (w : List Bool) : (pad w).length+1 = 2048*(w.length+1) := by
  simpa [pad] using repeated_length 11 w

theorem pad_length_bounds (w : List Bool) :
    w.length ≤ (pad w).length ∧ (pad w).length+2 ≤ 2049*(w.length+2) := by
  have := pad_length w
  omega

theorem box_width_fits {w : List Bool} {b : ℕ} (hb : b≤w.length+1) :
    5*PrimeAlgorithm.CertifiedCoordinateBounds.inputBits b+2 ≤ (pad w).length := by
  have := pad_length w
  unfold PrimeAlgorithm.CertifiedCoordinateBounds.inputBits
  omega

theorem query_width_fits {w : List Bool} {b : ℕ} (hb : b≤w.length+1) :
    24*PrimeAlgorithm.CertifiedCoordinateBounds.inputBits b ≤ (pad w).length := by
  have := pad_length w
  unfold PrimeAlgorithm.CertifiedCoordinateBounds.inputBits
  omega

theorem parameter_query_fits {w : List Bool} {b : ℕ} (hb : b≤w.length+1)
    (xs : List ℕ) (hlen : xs.length=24)
    (hx : ∀x∈xs,x<2^PrimeAlgorithm.CertifiedCoordinateBounds.inputBits b) :
    (encodeList xs).length ≤ (pad w).length := by
  rw [length_encodeList,hlen]
  apply le_trans (Nat.mul_le_mul_left 24 ?_) (query_width_fits hb)
  apply blockLen_le
  intro x hx'
  rw [← bits_eq_encodeNat]
  exact bits_length_le (hx x hx')

end EthFollowup.Primes.LinearPadding
