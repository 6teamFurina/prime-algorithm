import EthFollowup.Primes.FourKernelCount

set_option maxHeartbeats 3000000

namespace EthFollowup.Primes.FourKernel
open Finset EthFollowup.ModP EthFollowup.Factoring

theorem canonical_head_relations {P : Parameters} {br : Branch} {v : Base} {w : Weights}
    (hc : Core P br v) (hw : WeightBounds P br v w) :
    HeadRelations P br.unitD (extV 72 (canonical P br v w)) := by
  obtain ⟨hn,hd,hm,hN,he,hx,hy,hx1,hM,hM',hNN,hNN',hcop,hunit⟩ := hc.1
  have hcert := certificatePair_spec hx1 hn hcop
  have hlast : (if br.unitD then v 1=1 ∧ v 4=0 ∧
      (if br.unitD then 0 else (certificatePair (v 4) (v 1)).1)=0 ∧
      (if br.unitD then 0 else (certificatePair (v 4) (v 1)).2)=0
    else 2 ≤ v 1 ∧ 1 ≤ v 4 ∧
      CoprimeNode.Certificate (v 4) (v 1)
        (if br.unitD then 0 else (certificatePair (v 4) (v 1)).1)
        (if br.unitD then 0 else (certificatePair (v 4) (v 1)).2)) := by
    cases hu : br.unitD <;> simp only [hu,Bool.false_eq_true,↓reduceIte] at hunit ⊢
    · exact ⟨hunit.1,hunit.2.1,certificatePair_spec hunit.2.1 hunit.1 hunit.2.2⟩
    · simpa only [and_true] using hunit
  change 2 ≤ v 0 ∧ 1 ≤ v 1 ∧ 2 ≤ v 2 ∧ v 0 ≤ P.bound ∧ v 0=v 1*v 2 ∧
    v 0+v 3=v 0+v 3 ∧ v 1+v 4=v 1+v 4 ∧
    v 3<v 0 ∧ v 4<v 1 ∧ w 0<v 0 ∧ 1 ≤ v 3 ∧
    P.baseM ≤ v 2 ∧ v 2<2*P.baseM ∧ P.baseN ≤ v 0 ∧ v 0<2*P.baseN ∧
    CoprimeNode.Certificate (v 3) (v 0) (certificatePair (v 3) (v 0)).1
      (certificatePair (v 3) (v 0)).2 ∧ _
  exact ⟨hn,hd,hm,hN,he,rfl,rfl,hx,hy,hw.1,hx1,hM,hM',hNN,hNN',hcert,hlast⟩

/-- Every semantic base witness and every independent weight witness gives an
actual satisfying assignment of all 72 variables. -/
theorem canonical_relations {P : Parameters} {br : Branch} {v : Base} {w : Weights}
    (hc : Core P br v) (hw : WeightBounds P br v w) :
    Relations P br (extV 72 (canonical P br v w)) := by
  have hh := canonical_head_relations hc hw
  refine ⟨hh,fun k => ?_⟩
  have hs : kernelSlice (canonical P br v w) k =
      PhaseKernel.canonical (br.neg k) (br.imag k) (P.U k) (P.V k) (P.Q k)
        (kernelDenom P v k) (kernelNumer v k) P.scale (w k.succ) :=
    funext (kernelSlice_canonical P br v w k)
  have hlocal : PhaseKernel.InputRelations (br.neg k) (br.imag k)
      (P.U k) (P.V k) (P.Q k) (kernelDenom P v k) (kernelNumer v k) P.scale
      (kernelSlice (canonical P br v w) k) := by
    rw [hs]
    exact PhaseKernel.canonical_relations (hc.2 k).1 (hc.2 k).2 (hw.2 k)
  obtain ⟨h0,h1,h2,h3,h4,h5,hrel⟩ := hlocal
  refine ⟨?_,(kernelSlice_relations_iff _ _ _ k).1 hrel⟩
  have hx6 : canonical P br v w 6=canonical P br v w 0+canonical P br v w 3 :=
    hh.2.2.2.2.2.1
  have hx7 : canonical P br v w 7=canonical P br v w 1+canonical P br v w 4 :=
    hh.2.2.2.2.2.2.1
  have hden := denomValue_baseOf P (canonical P br v w) k
  have hnum := numerValue_baseOf (canonical P br v w) k hx6 hx7
  rw [baseOf_canonical] at hden hnum
  have hj (j : Fin 15) := extV_kernel (canonical P br v w) k j
  have hj0 : extV 72 (canonical P br v w) (offset k)=
      kernelSlice (canonical P br v w) k 0 := by simpa using hj 0
  exact ⟨hj0.trans h0,(hj 1).trans h1,(hj 2).trans h2,
    (hj 3).trans (h3.trans hden.symm),(hj 4).trans (h4.trans hnum.symm),(hj 5).trans h5⟩

/-- Uniform input bounds include the shifted phase numerators and doubled
bin endpoints. They determine the linear network size 5*B+2. -/
structure BitBounds (P : Parameters) (B : ℕ) : Prop where
  two : 2 ≤ 2^B
  bound : 2*P.bound ≤ 2^B
  baseM : 2*P.baseM ≤ 2^B
  baseN : 2*P.baseN ≤ 2^B
  scale : P.scale ≤ 2^B
  U : ∀k,P.U k ≤ 2^B
  V : ∀k,P.V k ≤ 2^B
  Q : ∀k,P.Q k ≤ 2^B

theorem base_coordinates_le {P : Parameters} {br : Branch} {v : Base}
    (h : BaseRelations P br v) : ∀i,v i ≤ P.bound := by
  obtain ⟨hn,hd,hm,hN,he,hx,hy,_⟩ := h
  have hdN : v 1 ≤ v 0 := by nlinarith
  have hmN : v 2 ≤ v 0 := by nlinarith
  intro i
  fin_cases i
  · exact hN
  · exact hdN.trans hN
  · exact hmN.trans hN
  · exact hx.le.trans hN
  · exact hy.le.trans (hdN.trans hN)

theorem head_coordinates_le {P : Parameters} {u : Bool} {x : ℕ → ℕ}
    (h : HeadRelations P u x) : ∀i<12,x i ≤ 2*P.bound := by
  obtain ⟨hn,hd,hm,hN,he,h6,h7,hx,hy,hw,hx1,hM,hM',hNN,hNN',hcop,hunit⟩ := h
  have hdN : x 1 ≤ x 0 := by nlinarith
  have hmN : x 2 ≤ x 0 := by nlinarith
  have h8 := hcop.1
  have h9 := hcop.2.1
  have h1011 : x 10 ≤ P.bound ∧ x 11 ≤ P.bound := by
    cases u <;> simp only [Bool.false_eq_true,↓reduceIte] at hunit
    · have hu := hunit.2.2.1
      have hv := hunit.2.2.2.1
      omega
    · omega
  intro i hi
  interval_cases i <;> omega

theorem kernel_inputs_le {P : Parameters} {br : Branch} {v : Base} {B : ℕ}
    (hb : BitBounds P B) (hc : Core P br v) (k : Fin 4) :
    kernelDenom P v k ≤ 2^B ∧ kernelNumer v k ≤ 2^B := by
  have hv := base_coordinates_le hc.1
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have hbound := hb.bound
  have hM := hb.baseM
  have hN := hb.baseN
  fin_cases k <;> simp [kernelDenom,kernelNumer] <;> omega

/-- The canonical assignment fits the real arithmetic box at linear bit size. -/
theorem canonical_lbox_bound {P : Parameters} {br : Branch} {v : Base} {w : Weights}
    {B : ℕ} (hb : BitBounds P B) (hc : Core P br v) (hw : WeightBounds P br v w) :
    ∀i,canonical P br v w i<lbox (5*B+2) 0 := by
  intro i
  by_cases hi : i.val<12
  · have hh := head_coordinates_le (canonical_head_relations hc hw) i.val hi
    have hval : canonical P br v w i ≤ 2^B := by
      have h : canonical P br v w i ≤ 2*P.bound := by simpa [extV,i.isLt] using hh
      exact h.trans hb.bound
    exact PhaseKernel.input_lbox_bound hval
  · let k : Fin 4 := ⟨(i.val-12)/15,by omega⟩
    let j : Fin 15 := ⟨(i.val-12)%15,Nat.mod_lt _ (by decide)⟩
    have he : (⟨offset k+j.val,by dsimp [offset]; omega⟩:Fin 72)=i := by
      apply Fin.ext
      dsimp [offset,k,j]
      omega
    have hinputs := kernel_inputs_le hb hc k
    have h := PhaseKernel.canonical_lbox_bound (hb.U k) (hb.V k) (hb.Q k)
      hinputs.1 hinputs.2 hb.scale (hc.2 k).1 (hc.2 k).2 (hw.2 k) j
    rw [←kernelSlice_canonical P br v w k j] at h
    simpa only [kernelSlice,he] using h

/-- The same bit bound validates every pinned constant of the full descriptor. -/
theorem bitBounds_fits {P : Parameters} {B : ℕ} (hb : BitBounds P B) :
    Fits P (b (5*B+2)) (kl (5*B+2) 0) where
  two := PhaseKernel.input_lbox_bound hb.two
  bound := PhaseKernel.input_lbox_bound (show P.bound ≤ 2^B by have := hb.bound; omega)
  baseM := PhaseKernel.input_lbox_bound (show P.baseM ≤ 2^B by have := hb.baseM; omega)
  baseN := PhaseKernel.input_lbox_bound (show P.baseN ≤ 2^B by have := hb.baseN; omega)
  twiceM := PhaseKernel.input_lbox_bound hb.baseM
  twiceN := PhaseKernel.input_lbox_bound hb.baseN
  scale := PhaseKernel.input_lbox_bound hb.scale
  U k := PhaseKernel.input_lbox_bound (hb.U k)
  V k := PhaseKernel.input_lbox_bound (hb.V k)
  Q k := PhaseKernel.input_lbox_bound (hb.Q k)

end EthFollowup.Primes.FourKernel
