/- A concrete bit-width choice for the exact Cauchy kernel network. -/
import EthFollowup.Primes.PhaseKernelCount
import EthFollowup.Primes.PhaseKernelBounds

namespace EthFollowup.Primes.PhaseKernel

open EthFollowup.ModP

/-- Every canonical quotient witness fits the network's real level-zero box. -/
theorem canonical_lbox_bound {neg imag : Bool} {B U V Q d t S w : ℕ}
    (hU : U≤2^B) (hV : V≤2^B) (hQ : Q≤2^B)
    (hd : d≤2^B) (ht : t≤2^B) (hS : S≤2^B)
    (hsign : if neg then U*d<Q*t else Q*t≤U*d)
    (hD : 0<denominator neg U V Q d t)
    (hw : w<quotient neg imag U V Q d t S) :
    ∀ j, canonical neg imag U V Q d t S w j<lbox (5*B+2) 0 := by
  obtain ⟨_,_,_,_,_,_,hr⟩ := canonical_relations hsign hD hw
  have hi : ∀ i<6, extV 15 (canonical neg imag U V Q d t S w) i≤2^B := by
    intro i hi
    interval_cases i <;> simp only [extV,canonical] <;> assumption
  intro j
  simpa [extV,j.isLt] using relations_lbox_bound hi hr j.val j.isLt

/-- Pin constants themselves also fit, including when the quotient has no witnesses. -/
theorem input_lbox_bound {B x : ℕ} (hx : x≤2^B) : x<lbox (5*B+2) 0 := by
  apply lbox_spec (5*B+2) 0
  simp only [pow_zero,pow_one]
  exact lt_of_le_of_lt hx (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- Exact reciprocal-component value at the explicit network size `5 * B + 2`.
    Only input bit bounds, the denominator condition, and the sign branch remain. -/
theorem actualNetwork_value_bit_bound (neg imag : Bool) {B g U V Q d t S : ℕ}
    (hg : 2≤g) (hU : U≤2^B) (hV : V≤2^B) (hQ : Q≤2^B)
    (hd : d≤2^B) (ht : t≤2^B) (hS : S≤2^B)
    (hsign : if neg then U*d<Q*t else Q*t≤U*d)
    (hD : 0<denominator neg U V Q d t) :
    ((arithSys (5*B+2) (actualDesc neg imag (5*B+2) U V Q d t S) g hg).net
      (aLabCode (5*B+2))).value = (quotient neg imag U V Q d t S : ℕ) := by
  apply actualNetwork_value neg imag hg (input_lbox_bound hU) (input_lbox_bound hV)
    (input_lbox_bound hQ) (input_lbox_bound hd) (input_lbox_bound ht)
    (input_lbox_bound hS) hsign hD
  intro w hw
  exact canonical_lbox_bound hU hV hQ hd ht hS hsign hD hw

/-- Value, communication, and engine parameters for the same concrete kernel net. -/
theorem actualNetwork_bit_spec (neg imag : Bool) {B g U V Q d t S : ℕ}
    (hg : 2≤g) (hU : U≤2^B) (hV : V≤2^B) (hQ : Q≤2^B)
    (hd : d≤2^B) (ht : t≤2^B) (hS : S≤2^B)
    (hsign : if neg then U*d<Q*t else Q*t≤U*d)
    (hD : 0<denominator neg U V Q d t) :
    let net := (arithSys (5*B+2) (actualDesc neg imag (5*B+2) U V Q d t S) g hg).net
      (aLabCode (5*B+2))
    net.value = (quotient neg imag U V Q d t S : ℕ) ∧
      net.U≤2^19*17*(5*B+4) ∧ net.Is (PL (5*B+2) 17 g) 1 := by
  exact ⟨actualNetwork_value_bit_bound neg imag hg hU hV hQ hd ht hS hsign hD,
    actualNetwork_communication neg imag hg, actualNetwork_is_PL neg imag hg⟩

end EthFollowup.Primes.PhaseKernel
