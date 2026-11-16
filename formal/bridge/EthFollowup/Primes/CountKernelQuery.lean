/- Query encoding and exact semantics of the concrete counted-network package. -/
import EthFollowup.Primes.CountKernelPoly
import EthFollowup.Primes.CountKernelPadding

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.CountKernel
open Groundwork EthFollowup.ModP EthFollowup.Factoring EthFollowup.ExactHC Finset

section Encode
variable {α : Type} [Enc α]

private theorem blockLen_le_flatten (l : List ℕ) :
    blockLen l ≤ (l.map Computability.encodeNat).flatten.length := by
  induction l with
  | nil => simp [blockLen]
  | cons a l ih =>
    simp only [blockLen,List.map_cons,List.foldr_cons,List.map_nil,List.foldr_nil,
      List.flatten_cons,List.length_append] at *
    omega

/-- Equal-width block encoding is itself a polynomial-time operation. -/
theorem encodeList_polyT {l : α → List ℕ} (hl : PolyT l) :
    PolyT fun x => encodeList (l x) := by
  have hbits : PolyT fun q : α × ℕ => Computability.encodeNat q.2 := by
    simpa only [←bits_eq_encodeNat] using PolyT.bits (PolyT.snd (PolyT.id' : PolyT (id : α × ℕ → α × ℕ)))
  have hwords : PolyT fun x => (l x).map Computability.encodeNat :=
    PolyT.map (f := fun _ v => Computability.encodeNat v) hbits hl
  have hlen : PolyT fun x => blockLen (l x) := by
    unfold blockLen
    exact Groundwork.Prog.NetE.foldr_max_polyT (PolyT.map
      (f := fun _ v => (Computability.encodeNat v).length) (PolyT.length hbits) hl)
  have hun : Unary fun x => blockLen (l x) :=
    Unary.of_le (Unary.of_length (PolyT.flatten hwords)) hlen
      (fun x => blockLen_le_flatten (l x))
  have hp : PolyT fun q : α × ℕ => padR (blockLen (l q.1)) (Computability.encodeNat q.2) := by
    have hfst : PolyT fun q : α × ℕ => q.1 := PolyT.fst PolyT.id'
    have hg : Unary fun q : α × ℕ => blockLen (l q.1)-(Computability.encodeNat q.2).length :=
      Unary.of_le (hun.comp hfst) (PolyT.sub (hlen.comp hfst) (PolyT.length hbits))
        (fun _ => Nat.sub_le _ _)
    have hz : PolyT fun q : α × ℕ => List.replicate
        (blockLen (l q.1)-(Computability.encodeNat q.2).length) false := by
      have hm := PolyT.map (f := fun _ (_ : Unit) => false) (PolyT.const false) hg
      exact hm.congr (fun _ => by simp)
    exact PolyT.append hbits hz
  exact PolyT.flatten (PolyT.map (f := fun x v => padR (blockLen (l x)) (Computability.encodeNat v)) hp hl)

theorem queryData_polyT {P : α → Parameters} {br : α → Branch}
    (hM : PolyT fun x => (P x).baseM) (hN : PolyT fun x => (P x).baseN)
    (hS : PolyT fun x => (P x).scale)
    (hU : ∀k,PolyT fun x => (P x).U k) (hV : ∀k,PolyT fun x => (P x).V k)
    (hQ : ∀k,PolyT fun x => (P x).Q k)
    (hu : PolyT fun x => (br x).unitD)
    (hn : ∀k,PolyT fun x => (br x).neg k) (hi : ∀k,PolyT fun x => (br x).imag k) :
    PolyT fun x => queryData (P x) (br x) := by
  unfold queryData
  fun_prop

theorem query_polyT {P : α → Parameters} {br : α → Branch}
    (hM : PolyT fun x => (P x).baseM) (hN : PolyT fun x => (P x).baseN)
    (hS : PolyT fun x => (P x).scale)
    (hU : ∀k,PolyT fun x => (P x).U k) (hV : ∀k,PolyT fun x => (P x).V k)
    (hQ : ∀k,PolyT fun x => (P x).Q k)
    (hu : PolyT fun x => (br x).unitD)
    (hn : ∀k,PolyT fun x => (br x).neg k) (hi : ∀k,PolyT fun x => (br x).imag k) :
    PolyT fun x => query (P x) (br x) :=
  encodeList_polyT (queryData_polyT hM hN hS hU hV hQ hu hn hi)
end Encode

/-- Exact full weighted count, at any sufficient input length. -/
theorem reader_query_count {P : Parameters} {br : Branch} {B : ℕ} (w : List Bool)
    (hN : Groundwork.ofWord w=P.bound) (hb : BitBounds P B) (hn : 5*B+2≤w.length) :
    (reader (w,query P br)).count w.length =
      ∑v∈bases P br,∏k,kernelQuotient P br v k := by
  unfold reader
  rw [readParameters_query P br w hN,readBranch_query]
  exact descriptor_count (lbox w.length) (bitBounds_fits_at hb hn)
    (fun v hc w hw => canonical_lbox_bound_at hb hn hc hw)

/-- The same package has the full four-kernel semantics on every valid encoding. -/
theorem package_exact_exists :
    ∃pk : CntPackage (2^22*132),
      (∀w,pk.R w=w.length) ∧ (∀w,pk.Ok w) ∧ pk.qb=2^13*132+1 ∧
      ∀(P : Parameters) (br : Branch) (B : ℕ) (w : List Bool),
        Groundwork.ofWord w=P.bound → BitBounds P B → 5*B+2≤w.length →
        pk.Q w (query P br)=∑v∈bases P br,∏k,kernelQuotient P br v k := by
  obtain ⟨pk,hQ,hR,hOk,hqb⟩ := package_exists
  refine ⟨pk,hR,hOk,hqb,?_⟩
  intro P br B w hN hb hn
  rw [hQ]
  exact reader_query_count w hN hb hn

end EthFollowup.Primes.CountKernel
