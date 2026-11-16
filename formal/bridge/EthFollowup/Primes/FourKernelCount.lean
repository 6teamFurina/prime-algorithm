/- Exact witness decomposition for the concrete four-kernel descriptor. -/
import EthFollowup.Primes.FourKernelDesc

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.FourKernel
open Finset EthFollowup.ModP

abbrev Base := Fin 5 → ℕ
abbrev Weights := Fin 5 → ℕ

def kernelDenom (P : Parameters) (v : Base) (k : Fin 4) : ℕ :=
  match k.val with | 0 => P.baseM | 1 => P.baseN | 2 => v 0 | _ => v 1

def kernelNumer (v : Base) (k : Fin 4) : ℕ :=
  match k.val with | 0 => v 2 | 1 => v 0 | 2 => v 0+v 3 | _ => v 1+v 4

def kernelQuotient (P : Parameters) (br : Branch) (v : Base) (k : Fin 4) : ℕ :=
  PhaseKernel.quotient (br.neg k) (br.imag k) (P.U k) (P.V k) (P.Q k)
    (kernelDenom P v k) (kernelNumer v k) P.scale

def BaseRelations (P : Parameters) (br : Branch) (v : Base) : Prop :=
  2≤v 0 ∧ 1≤v 1 ∧ 2≤v 2 ∧ v 0≤P.bound ∧ v 0=v 1*v 2 ∧
  v 3<v 0 ∧ v 4<v 1 ∧ 1≤v 3 ∧
  P.baseM≤v 2 ∧ v 2<2*P.baseM ∧ P.baseN≤v 0 ∧ v 0<2*P.baseN ∧
  (v 3).Coprime (v 0) ∧
  if br.unitD then v 1=1 ∧ v 4=0
  else 2≤v 1 ∧ 1≤v 4 ∧ (v 4).Coprime (v 1)

def Core (P : Parameters) (br : Branch) (v : Base) : Prop :=
  BaseRelations P br v ∧ ∀k,
    (if br.neg k then P.U k*kernelDenom P v k<P.Q k*kernelNumer v k
      else P.Q k*kernelNumer v k≤P.U k*kernelDenom P v k) ∧
    0<PhaseKernel.denominator (br.neg k) (P.U k) (P.V k) (P.Q k)
      (kernelDenom P v k) (kernelNumer v k)

def WeightBounds (P : Parameters) (br : Branch) (v : Base) (w : Weights) : Prop :=
  w 0<v 0 ∧ ∀k,w k.succ<kernelQuotient P br v k

noncomputable def certificatePair (a b : ℕ) : ℕ × ℕ := by
  classical
  exact if h : 1≤a ∧ 2≤b ∧ a.Coprime b then
    Classical.choose (show ∃p:ℕ×ℕ,CoprimeNode.Certificate a b p.1 p.2 by
      obtain ⟨u,v,hc⟩ := CoprimeNode.certificate_exists_of_one_le h.1 h.2.1 h.2.2
      exact ⟨(u,v),hc⟩) else (0,0)

theorem certificatePair_spec {a b : ℕ} (ha : 1≤a) (hb : 2≤b) (hc : a.Coprime b) :
    CoprimeNode.Certificate a b (certificatePair a b).1 (certificatePair a b).2 := by
  classical
  unfold certificatePair
  rw [dif_pos ⟨ha,hb,hc⟩]
  exact Classical.choose_spec (show ∃p:ℕ×ℕ,CoprimeNode.Certificate a b p.1 p.2 by
    obtain ⟨u,v,h⟩ := CoprimeNode.certificate_exists_of_one_le ha hb hc
    exact ⟨(u,v),h⟩)

noncomputable def headCanonical (br : Branch) (v : Base) (w : Weights) (i : Fin 12) : ℕ :=
  match i.val with
  | 0 => v 0 | 1 => v 1 | 2 => v 2 | 3 => v 3 | 4 => v 4 | 5 => w 0
  | 6 => v 0+v 3 | 7 => v 1+v 4
  | 8 => (certificatePair (v 3) (v 0)).1
  | 9 => (certificatePair (v 3) (v 0)).2
  | 10 => if br.unitD then 0 else (certificatePair (v 4) (v 1)).1
  | _ => if br.unitD then 0 else (certificatePair (v 4) (v 1)).2

noncomputable def canonical (P : Parameters) (br : Branch) (v : Base) (w : Weights)
    (i : Fin 72) : ℕ :=
  if h : i.val<12 then headCanonical br v w ⟨i.val,h⟩ else
    let k : Fin 4 := ⟨(i.val-12)/15,by omega⟩
    PhaseKernel.canonical (br.neg k) (br.imag k) (P.U k) (P.V k) (P.Q k)
      (kernelDenom P v k) (kernelNumer v k) P.scale (w k.succ)
      ⟨(i.val-12)%15,Nat.mod_lt _ (by decide)⟩

def headSlice (x : Fin 72 → ℕ) (i : Fin 12) : ℕ := x ⟨i.val,by omega⟩
def kernelSlice (x : Fin 72 → ℕ) (k : Fin 4) (j : Fin 15) : ℕ :=
  x ⟨offset k+j.val,by dsimp [offset]; omega⟩
def baseOf (x : Fin 72 → ℕ) (i : Fin 5) : ℕ := x ⟨i.val,by omega⟩
def weightsOf (x : Fin 72 → ℕ) : Weights :=
  Fin.cons (x 5) (fun k : Fin 4 => kernelSlice x k 14)

@[simp] theorem headSlice_canonical (P : Parameters) (br : Branch) (v : Base) (w : Weights)
    (i : Fin 12) : headSlice (canonical P br v w) i=headCanonical br v w i := by
  simp [headSlice,canonical,i.isLt]

@[simp] theorem kernelSlice_canonical (P : Parameters) (br : Branch) (v : Base) (w : Weights)
    (k : Fin 4) (j : Fin 15) :
    kernelSlice (canonical P br v w) k j=
      PhaseKernel.canonical (br.neg k) (br.imag k) (P.U k) (P.V k) (P.Q k)
        (kernelDenom P v k) (kernelNumer v k) P.scale (w k.succ) j := by
  unfold kernelSlice canonical
  rw [dif_neg (by dsimp [offset]; omega)]
  have hk : (⟨(offset k+j.val-12)/15,by dsimp [offset]; omega⟩:Fin 4)=k := by
    apply Fin.ext
    dsimp [offset]
    omega
  simp only [hk]
  congr 1
  apply Fin.ext
  dsimp [offset]
  omega

theorem layout_ext {x y : Fin 72 → ℕ}
    (hh : ∀i,headSlice x i=headSlice y i)
    (hk : ∀k j,kernelSlice x k j=kernelSlice y k j) : x=y := by
  funext i
  by_cases hi : i.val<12
  · exact hh ⟨i.val,hi⟩
  · let k : Fin 4 := ⟨(i.val-12)/15,by omega⟩
    let j : Fin 15 := ⟨(i.val-12)%15,Nat.mod_lt _ (by decide)⟩
    have he : (⟨offset k+j.val,by dsimp [offset]; omega⟩:Fin 72)=i := by
      apply Fin.ext
      dsimp [offset,k,j]
      omega
    have h := hk k j
    simpa only [kernelSlice,he] using h

@[simp] theorem baseOf_canonical (P : Parameters) (br : Branch) (v : Base) (w : Weights) :
    baseOf (canonical P br v w)=v := by
  funext i
  have h := headSlice_canonical P br v w ⟨i.val,by omega⟩
  change canonical P br v w ⟨i.val,by omega⟩=v i
  rw [show canonical P br v w ⟨i.val,by omega⟩ =
    headCanonical br v w ⟨i.val,by omega⟩ from h]
  fin_cases i <;> rfl

@[simp] theorem weightsOf_canonical (P : Parameters) (br : Branch) (v : Base) (w : Weights) :
    weightsOf (canonical P br v w)=w := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · change headSlice (canonical P br v w) 5=w 0
    rw [headSlice_canonical]
    rfl
  · simp [weightsOf,kernelSlice_canonical,PhaseKernel.canonical]

@[simp] theorem extV_head (x : Fin 72 → ℕ) (i : Fin 12) :
    extV 72 x i.val=headSlice x i := by
  simp [extV,headSlice,show i.val<72 by omega]

@[simp] theorem extV_kernel (x : Fin 72 → ℕ) (k : Fin 4) (j : Fin 15) :
    extV 72 x (offset k+j.val)=kernelSlice x k j := by
  simp [extV,kernelSlice,show offset k+j.val<72 by dsimp [offset]; omega]

theorem phase_relations_congr {neg imag : Bool} {x y : ℕ → ℕ}
    (h : ∀i<15,x i=y i) : PhaseKernel.Relations neg imag x ↔ PhaseKernel.Relations neg imag y := by
  simp only [PhaseKernel.Relations,
    h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 4 (by decide),
    h 5 (by decide),h 6 (by decide),h 7 (by decide),h 8 (by decide),h 9 (by decide),
    h 10 (by decide),h 11 (by decide),h 12 (by decide),h 13 (by decide),h 14 (by decide)]

theorem kernelSlice_relations_iff (neg imag : Bool) (x : Fin 72 → ℕ) (k : Fin 4) :
    PhaseKernel.Relations neg imag (extV 15 (kernelSlice x k)) ↔
      PhaseKernel.Relations neg imag (fun i => extV 72 x (offset k+i)) := by
  apply phase_relations_congr
  intro i hi
  simpa [extV,hi,kernelSlice,show offset k+i<72 by dsimp [offset]; omega]

theorem denomValue_baseOf (P : Parameters) (x : Fin 72 → ℕ) (k : Fin 4) :
    denomValue P k (extV 72 x)=kernelDenom P (baseOf x) k := by
  fin_cases k <;> simp [denomValue,kernelDenom,baseOf,extV]

theorem numerValue_baseOf (x : Fin 72 → ℕ) (k : Fin 4)
    (h6 : x 6=x 0+x 3) (h7 : x 7=x 1+x 4) :
    numerValue k (extV 72 x)=kernelNumer (baseOf x) k := by
  fin_cases k <;> simp [numerValue,kernelNumer,baseOf,extV,h6,h7]

theorem local_inputRelations {P : Parameters} {br : Branch} {x : Fin 72 → ℕ}
    (hr : Relations P br (extV 72 x)) (k : Fin 4) :
    PhaseKernel.InputRelations (br.neg k) (br.imag k) (P.U k) (P.V k) (P.Q k)
      (kernelDenom P (baseOf x) k) (kernelNumer (baseOf x) k) P.scale (kernelSlice x k) := by
  obtain ⟨_,_,_,_,_,h6,h7,_⟩ := hr.1
  change x 6=x 0+x 3 at h6
  change x 7=x 1+x 4 at h7
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := (hr.2 k).1
  have he (j : Fin 15) := extV_kernel x k j
  have he0 : extV 72 x (offset k)=kernelSlice x k 0 := by simpa using he 0
  refine ⟨?_,?_,?_,?_,?_,?_,(kernelSlice_relations_iff _ _ x k).2 (hr.2 k).2⟩
  · exact he0.symm.trans h0
  · exact (he 1).symm.trans h1
  · exact (he 2).symm.trans h2
  · exact (he 3).symm.trans (h3.trans (denomValue_baseOf P x k))
  · exact (he 4).symm.trans (h4.trans (numerValue_baseOf x k h6 h7))
  · exact (he 5).symm.trans h5

theorem relations_base {P : Parameters} {br : Branch} {x : Fin 72 → ℕ}
    (hr : Relations P br (extV 72 x)) : BaseRelations P br (baseOf x) := by
  obtain ⟨hn,hd,hm,hN,he,h6,h7,hx,hy,hw,hx1,hM,hM',hNN,hNN',hcop,hunit⟩ := hr.1
  refine ⟨hn,hd,hm,hN,he,hx,hy,hx1,hM,hM',hNN,hNN',hcop.coprime,?_⟩
  cases hu : br.unitD <;> simp only [hu,Bool.false_eq_true,↓reduceIte] at hunit ⊢
  · exact ⟨hunit.1,hunit.2.1,hunit.2.2.coprime⟩
  · exact ⟨hunit.1,hunit.2.1⟩

theorem relations_core {P : Parameters} {br : Branch} {x : Fin 72 → ℕ}
    (hr : Relations P br (extV 72 x)) : Core P br (baseOf x) := by
  refine ⟨relations_base hr,fun k => ?_⟩
  have hl := local_inputRelations hr k
  have he := PhaseKernel.inputRelations_unique (kernelSlice x k) hl
  obtain ⟨hu,hv,hq,hd,ht,hs,hrel⟩ := hl
  obtain ⟨hsgn,_,_,_,_,_,_,hD,_,_⟩ := hrel
  have hD' := congrArg (fun f : Fin 15 → ℕ => f 8) he
  change kernelSlice x k 8=PhaseKernel.denominator (br.neg k) (P.U k) (P.V k) (P.Q k)
    (kernelDenom P (baseOf x) k) (kernelNumer (baseOf x) k) at hD'
  change 1≤kernelSlice x k 8 at hD
  refine ⟨?_,by rw [←hD']; omega⟩
  change (if br.neg k then kernelSlice x k 0*kernelSlice x k 3+kernelSlice x k 6=
    kernelSlice x k 2*kernelSlice x k 4 ∧ 1≤kernelSlice x k 6
    else kernelSlice x k 0*kernelSlice x k 3=kernelSlice x k 2*kernelSlice x k 4+kernelSlice x k 6) at hsgn
  rw [hu,hq,hd,ht] at hsgn
  cases hn : br.neg k <;> simp only [hn,Bool.false_eq_true,↓reduceIte] at hsgn ⊢ <;> omega

theorem relations_weights {P : Parameters} {br : Branch} {x : Fin 72 → ℕ}
    (hr : Relations P br (extV 72 x)) : WeightBounds P br (baseOf x) (weightsOf x) := by
  refine ⟨?_,fun k => ?_⟩
  · obtain ⟨_,_,_,_,_,_,_,_,_,hw,_⟩ := hr.1
    exact hw
  · simpa [weightsOf,kernelQuotient] using
      PhaseKernel.inputRelations_weight (kernelSlice x k) (local_inputRelations hr k)

theorem assignment_eq_canonical {P : Parameters} {br : Branch} {x : Fin 72 → ℕ}
    (hr : Relations P br (extV 72 x)) : x=canonical P br (baseOf x) (weightsOf x) := by
  obtain ⟨hn,hd,hm,hN,he,h6,h7,hx,hy,hw,hx1,hM,hM',hNN,hNN',hcop,hunit⟩ := hr.1
  change CoprimeNode.Certificate (x 3) (x 0) (x 8) (x 9) at hcop
  change 2≤x 0 at hn
  change 1≤x 3 at hx1
  change x 6=x 0+x 3 at h6
  change x 7=x 1+x 4 at h7
  have hcN := certificatePair_spec hx1 hn hcop.coprime
  obtain ⟨h8,h9⟩ := hcop.unique (by omega) hcN
  have h10 : x 10=(if br.unitD then 0 else (certificatePair (x 4) (x 1)).1) := by
    cases hu : br.unitD <;> simp only [hu,Bool.false_eq_true,↓reduceIte] at hunit ⊢
    · exact (hunit.2.2.unique (by exact lt_of_lt_of_le (by decide : 0<2) hunit.1)
        (certificatePair_spec hunit.2.1 hunit.1 hunit.2.2.coprime)).1
    · exact hunit.2.2.1
  have h11 : x 11=(if br.unitD then 0 else (certificatePair (x 4) (x 1)).2) := by
    cases hu : br.unitD <;> simp only [hu,Bool.false_eq_true,↓reduceIte] at hunit ⊢
    · exact (hunit.2.2.unique (by exact lt_of_lt_of_le (by decide : 0<2) hunit.1)
        (certificatePair_spec hunit.2.1 hunit.1 hunit.2.2.coprime)).2
    · exact hunit.2.2.2
  apply layout_ext
  · intro i
    rw [headSlice_canonical]
    fin_cases i <;> simp [headSlice,headCanonical,baseOf,weightsOf,h6,h7,h8,h9,h10,h11]
  · intro k j
    rw [kernelSlice_canonical]
    have h := congrArg (fun f : Fin 15 → ℕ => f j)
      (PhaseKernel.inputRelations_unique (kernelSlice x k) (local_inputRelations hr k))
    simpa [weightsOf] using h

end EthFollowup.Primes.FourKernel
