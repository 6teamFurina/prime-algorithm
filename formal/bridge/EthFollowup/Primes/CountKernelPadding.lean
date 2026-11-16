import EthFollowup.Primes.CountKernelCountFinal

/-! The unweighted four-kernel count remains exact when the machine uses a
larger linearly padded input size. -/
namespace EthFollowup.Primes.CountKernel
open Finset EthFollowup.ModP EthFollowup.Factoring EthFollowup.ExactHC

theorem input_lbox_bound_at {B n x : ℕ} (hn : 5*B+2≤n) (hx : x≤2^B) : x<lbox n 0 := by
  apply lbox_spec n 0
  simp only [pow_zero,pow_one]
  exact lt_of_le_of_lt hx (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem phase_canonical_pow_bound {neg imag : Bool} {B U V Q d t S w : ℕ}
    (hU : U≤2^B) (hV : V≤2^B) (hQ : Q≤2^B) (hd : d≤2^B) (ht : t≤2^B) (hS : S≤2^B)
    (hsign : if neg then U*d<Q*t else Q*t≤U*d)
    (hD : 0<PhaseKernel.denominator neg U V Q d t)
    (hw : w<PhaseKernel.quotient neg imag U V Q d t S) :
    ∀j,PhaseKernel.canonical neg imag U V Q d t S w j<2^(5*B+2) := by
  obtain ⟨_,_,_,_,_,_,hr⟩ := PhaseKernel.canonical_relations hsign hD hw
  have hi : ∀i<6,extV 15 (PhaseKernel.canonical neg imag U V Q d t S w) i≤2^B := by
    intro i hi
    interval_cases i <;> simp only [extV,PhaseKernel.canonical] <;> assumption
  intro j
  simpa [extV,j.isLt] using PhaseKernel.relations_bit_bound hi hr j.val j.isLt

theorem canonical_lbox_bound_at {P : Parameters} {br : Branch} {v : Base} {w : Weights}
    {B n : ℕ} (hb : BitBounds P B) (hn : 5*B+2≤n)
    (hc : Core P br v) (hw : WeightBounds P br v w) :
    ∀i,canonical P br v w i<lbox n 0 := by
  intro i
  by_cases hi : i.val<12
  · have hh := head_coordinates_le (canonical_head_relations hc hw) i.val hi
    have hval : canonical P br v w i ≤ 2^B := by
      have h : canonical P br v w i ≤ 2*P.bound := by simpa [extV,i.isLt] using hh
      exact h.trans hb.bound
    exact input_lbox_bound_at hn hval
  · let k : Fin 4 := ⟨(i.val-12)/15,by omega⟩
    let j : Fin 15 := ⟨(i.val-12)%15,Nat.mod_lt _ (by decide)⟩
    have he : (⟨offset k+j.val,by dsimp [offset]; omega⟩:Fin 72)=i := by
      apply Fin.ext
      dsimp [offset,k,j]
      omega
    have hinputs := kernel_inputs_le hb hc k
    have h := phase_canonical_pow_bound (hb.U k) (hb.V k) (hb.Q k)
      hinputs.1 hinputs.2 hb.scale (hc.2 k).1 (hc.2 k).2 (hw.2 k) j
    rw [←kernelSlice_canonical P br v w k j] at h
    have hi' : canonical P br v w i<2^(5*B+2) := by
      simpa only [kernelSlice,he] using h
    apply lbox_spec n 0
    simpa using hi'.trans_le (Nat.pow_le_pow_right (by decide) hn)

theorem bitBounds_fits_at {P : Parameters} {B n : ℕ} (hb : BitBounds P B)
    (hn : 5*B+2≤n) : Fits P (b n) (kl n 0) where
  two := input_lbox_bound_at hn hb.two
  bound := input_lbox_bound_at hn (show P.bound ≤ 2^B by have := hb.bound; omega)
  baseM := input_lbox_bound_at hn (show P.baseM ≤ 2^B by have := hb.baseM; omega)
  baseN := input_lbox_bound_at hn (show P.baseN ≤ 2^B by have := hb.baseN; omega)
  twiceM := input_lbox_bound_at hn hb.baseM
  twiceN := input_lbox_bound_at hn hb.baseN
  scale := input_lbox_bound_at hn hb.scale
  U k := input_lbox_bound_at hn (hb.U k)
  V k := input_lbox_bound_at hn (hb.V k)
  Q k := input_lbox_bound_at hn (hb.Q k)

theorem actualNetwork_bit_spec_at {P : Parameters} {br : Branch} {B n g : ℕ}
    (hb : BitBounds P B) (hn : 5*B+2≤n) (hg : 2≤g) :
    let net := (arithSys n (actualDesc P br n) g hg).net (aLabCode n)
    net.value = ((∑v∈bases P br,∏k,kernelQuotient P br v k : ℕ) : ℤ) ∧
      net.U≤2^19*132*(n+2) ∧ net.Is (PL n 132 g) 1 := by
  refine ⟨actualNetwork_value hg (bitBounds_fits_at hb hn) ?_,
    actualNetwork_communication P br hg,actualNetwork_is P br hg⟩
  intro v hc w hw
  exact canonical_lbox_bound_at hb hn hc hw

end EthFollowup.Primes.CountKernel
