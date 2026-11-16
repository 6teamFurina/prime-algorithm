/- Concrete, uniform bit-width bounds for the Cauchy reciprocal component. -/
import EthFollowup.Primes.PhaseKernelDesc

set_option maxHeartbeats 800000

namespace EthFollowup.Primes.PhaseKernel

open EthFollowup.ExactHC EthFollowup.ModP

/-- Arithmetic closure of the kernel equations, permitting the endpoint weight `w=q`.
    This supplies a canonical zero-weight size bound even when the quotient is zero. -/
def RelationsClosed (neg imag : Bool) (x : ℕ → ℕ) : Prop :=
  (if neg then x 0*x 3+x 6=x 2*x 4 ∧ 1≤x 6 else x 0*x 3=x 2*x 4+x 6) ∧
  x 7=x 1*x 3 ∧ x 8=x 6*x 6+x 7*x 7 ∧ x 9=x 2*x 3 ∧
  x 10=x 9*(if imag then x 7 else x 6) ∧ x 11=x 5*x 10 ∧
  x 11=x 8*x 12+x 13 ∧ 1≤x 8 ∧ x 13<x 8 ∧ x 14≤x 12

theorem relations_closed {neg imag : Bool} {x : ℕ → ℕ}
    (h : Relations neg imag x) : RelationsClosed neg imag x := by
  rcases h with ⟨hs,h7,h8,h9,h10,h11,hqr,hD,hr,hw⟩
  exact ⟨hs,h7,h8,h9,h10,h11,hqr,hD,hr,le_of_lt hw⟩

/-- Every auxiliary variable, including the quotient weight witness, has polynomial
    magnitude of degree at most five in a common bound for the six inputs. -/
theorem closed_relations_coordinate_bound {neg imag : Bool} {x : ℕ → ℕ} {R : ℕ}
    (hR : 1≤R) (hi : ∀ i<6, x i≤R) (hr : RelationsClosed neg imag x) :
    ∀ i<15, x i≤2*R^5 := by
  obtain ⟨hs,h7,h8,h9,h10,h11,hqr,hD,hrD,hw⟩ := hr
  have h03 : x 0*x 3≤R^2 := by nlinarith [Nat.mul_le_mul (hi 0 (by decide)) (hi 3 (by decide))]
  have h24 : x 2*x 4≤R^2 := by nlinarith [Nat.mul_le_mul (hi 2 (by decide)) (hi 4 (by decide))]
  have ha : x 6≤R^2 := by
    cases neg <;> simp at hs <;> omega
  have hb : x 7≤R^2 := by
    rw [h7]
    nlinarith [Nat.mul_le_mul (hi 1 (by decide)) (hi 3 (by decide))]
  have hden : x 8≤2*R^4 := by
    rw [h8]
    calc
      x 6*x 6+x 7*x 7 ≤ R^2*R^2+R^2*R^2 :=
        Nat.add_le_add (Nat.mul_le_mul ha ha) (Nat.mul_le_mul hb hb)
      _ = 2*R^4 := by ring
  have hbase : x 9≤R^2 := by
    rw [h9]
    nlinarith [Nat.mul_le_mul (hi 2 (by decide)) (hi 3 (by decide))]
  have hnum : x 10≤R^4 := by
    rw [h10]
    cases imag <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · nlinarith [Nat.mul_le_mul hbase ha]
    · nlinarith [Nat.mul_le_mul hbase hb]
  have hscaled : x 11≤R^5 := by
    rw [h11]
    nlinarith [Nat.mul_le_mul (hi 5 (by decide)) hnum]
  have hq : x 12≤x 11 := by
    have := Nat.mul_le_mul_right (x 12) hD
    nlinarith
  have hrem : x 13≤x 11 := by omega
  have hw' : x 14≤x 11 := by omega
  have hR2 : R≤R^2 := by nlinarith
  have hR4 : R^2≤R^4 := by nlinarith [Nat.pow_le_pow_left hR2 2]
  have hR5 : R^4≤R^5 := by nlinarith [Nat.mul_le_mul_right (R^4) hR]
  intro i hit
  interval_cases i <;> first | exact (hi _ (by decide)).trans (by omega) | omega

theorem relations_coordinate_bound {neg imag : Bool} {x : ℕ → ℕ} {R : ℕ}
    (hR : 1≤R) (hi : ∀ i<6, x i≤R) (hr : Relations neg imag x) :
    ∀ i<15, x i≤2*R^5 :=
  closed_relations_coordinate_bound hR hi (relations_closed hr)

/-- The component uses at most `5 * B + 2` bits per variable when each input
    is at most `2^B`. This bound is independent of the reciprocal denominator. -/
theorem closed_relations_bit_bound {neg imag : Bool} {x : ℕ → ℕ} {B : ℕ}
    (hi : ∀ i<6, x i≤2^B) (hr : RelationsClosed neg imag x) :
    ∀ i<15, x i<2^(5*B+2) := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by omega)
  intro i hi'
  have hx := closed_relations_coordinate_bound hp hi hr i hi'
  have he : 2*(2^B)^5 < 2^(5*B+2) := by
    rw [← Nat.pow_mul, Nat.mul_comm B 5, pow_add]
    have hpos : 0<2^(5*B) := by positivity
    norm_num
    omega
  exact lt_of_le_of_lt hx he

theorem relations_bit_bound {neg imag : Bool} {x : ℕ → ℕ} {B : ℕ}
    (hi : ∀ i<6, x i≤2^B) (hr : Relations neg imag x) :
    ∀ i<15, x i<2^(5*B+2) :=
  closed_relations_bit_bound hi (relations_closed hr)

/-- Choosing the network size `5 * B + 2` places all variables in its actual
    level-zero arithmetic box; no separate auxiliary-size hypothesis is needed. -/
theorem relations_lbox_bound {neg imag : Bool} {x : ℕ → ℕ} {B : ℕ}
    (hi : ∀ i<6, x i≤2^B) (hr : Relations neg imag x) :
    ∀ i<15, x i<lbox (5*B+2) 0 := by
  intro i hi'
  apply lbox_spec (5*B+2) 0
  simpa using relations_bit_bound hi hr i hi'

theorem closed_relations_lbox_bound {neg imag : Bool} {x : ℕ → ℕ} {B : ℕ}
    (hi : ∀ i<6, x i≤2^B) (hr : RelationsClosed neg imag x) :
    ∀ i<15, x i<lbox (5*B+2) 0 := by
  intro i hi'
  apply lbox_spec (5*B+2) 0
  simpa using closed_relations_bit_bound hi hr i hi'

/-- The actual kernel network has linear total communication in its input bit width. -/
theorem actualNetwork_communication (neg imag : Bool) {n g U V Q d t S : ℕ}
    (hg : 2≤g) :
    ((arithSys n (actualDesc neg imag n U V Q d t S) g hg).net (aLabCode n)).U ≤
      2^19*17*(n+2) := by
  apply arithSys_U_le hg (actualDesc_WF neg imag n U V Q d t S)
    (actualDesc_spread neg imag n U V Q d t S) (by norm_num)
  simp [actualDesc,pinnedDesc,mkDesc,LDesc.nL]

/-- The fixed spread gives the original engine's explicit node bound. -/
theorem actualNetwork_is_PL (neg imag : Bool) {n g U V Q d t S : ℕ}
    (hg : 2≤g) :
    ((arithSys n (actualDesc neg imag n U V Q d t S) g hg).net (aLabCode n)).Is
      (PL n 17 g) 1 := by
  apply arithSys_is hg (actualDesc_WF neg imag n U V Q d t S)
    (actualDesc_spread neg imag n U V Q d t S) (by norm_num)
  simp [actualDesc,pinnedDesc,mkDesc,LDesc.nL]

end EthFollowup.Primes.PhaseKernel
