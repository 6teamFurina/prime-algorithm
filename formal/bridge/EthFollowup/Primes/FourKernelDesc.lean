/- Four actual reciprocal kernels sharing the prime-sum witness n,d,m,x,y. -/
import EthFollowup.Primes.FourKernelCompiler

set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.FourKernel
open Finset EthFollowup.ModP

structure Parameters where
  bound : ℕ
  baseM : ℕ
  baseN : ℕ
  scale : ℕ
  U : Fin 4 → ℕ
  V : Fin 4 → ℕ
  Q : Fin 4 → ℕ

structure Branch where
  unitD : Bool
  neg : Fin 4 → Bool
  imag : Fin 4 → Bool

def zeroProd : ProdD := ⟨0,.const []⟩
def linearProd (v : ℕ) : ProdD := ⟨v,.const [1]⟩
def mulProd (u v : ℕ) : ProdD := ⟨u,.var v⟩
def offset (k : Fin 4) : ℕ := 12+15*k.val

def headEquations (unitD : Bool) : Fin 5 → Equation
  | 0 => ⟨linearProd 0,zeroProd,mulProd 1 2,zeroProd,[],[]⟩
  | 1 => ⟨linearProd 6,zeroProd,linearProd 0,linearProd 3,[],[]⟩
  | 2 => ⟨linearProd 7,zeroProd,linearProd 1,linearProd 4,[],[]⟩
  | 3 => ⟨mulProd 3 8,zeroProd,mulProd 0 9,zeroProd,[],[1]⟩
  | _ => ⟨mulProd 4 10,zeroProd,mulProd 1 11,zeroProd,[],if unitD then [] else [1]⟩

def kernelEquations (neg imag : Bool) (o : ℕ) : Fin 7 → Equation
  | 0 => if neg then
      ⟨mulProd o (o+3),linearProd (o+6),mulProd (o+2) (o+4),zeroProd,[],[]⟩ else
      ⟨mulProd o (o+3),zeroProd,mulProd (o+2) (o+4),linearProd (o+6),[],[]⟩
  | 1 => ⟨linearProd (o+7),zeroProd,mulProd (o+1) (o+3),zeroProd,[],[]⟩
  | 2 => ⟨linearProd (o+8),zeroProd,mulProd (o+6) (o+6),mulProd (o+7) (o+7),[],[]⟩
  | 3 => ⟨linearProd (o+9),zeroProd,mulProd (o+2) (o+3),zeroProd,[],[]⟩
  | 4 => ⟨linearProd (o+10),zeroProd,mulProd (o+9) (o+(if imag then 7 else 6)),zeroProd,[],[]⟩
  | 5 => ⟨linearProd (o+11),zeroProd,mulProd (o+5) (o+10),zeroProd,[],[]⟩
  | _ => ⟨linearProd (o+11),zeroProd,mulProd (o+8) (o+12),linearProd (o+13),[],[]⟩

def equations (br : Branch) (c : Fin 33) : Equation :=
  if h : c.val<5 then headEquations br.unitD ⟨c.val,h⟩ else
    let k : Fin 4 := ⟨(c.val-5)/7,by omega⟩
    kernelEquations (br.neg k) (br.imag k) (offset k)
      ⟨(c.val-5)%7,Nat.mod_lt _ (by decide)⟩

def headComparisons (P : Parameters) (unitD : Bool) (b l : ℕ) : List CmpD :=
  [⟨0,.const (toLimbs b l 2),.ge⟩,⟨1,.const [1],.ge⟩,
   ⟨2,.const (toLimbs b l 2),.ge⟩,⟨0,.const (toLimbs b l P.bound),.le⟩,
   ⟨3,.var 0,.lt⟩,⟨4,.var 1,.lt⟩,⟨5,.var 0,.lt⟩,⟨3,.const [1],.ge⟩,
   ⟨8,.var 0,.lt⟩,⟨9,.var 3,.lt⟩,
   ⟨2,.const (toLimbs b l P.baseM),.ge⟩,⟨2,.const (toLimbs b l (2*P.baseM)),.lt⟩,
   ⟨0,.const (toLimbs b l P.baseN),.ge⟩,⟨0,.const (toLimbs b l (2*P.baseN)),.lt⟩] ++
  if unitD then
    [⟨1,.const [1],.eq⟩,⟨4,.const [],.eq⟩,⟨10,.const [],.eq⟩,⟨11,.const [],.eq⟩]
  else [⟨1,.const (toLimbs b l 2),.ge⟩,⟨4,.const [1],.ge⟩,
    ⟨10,.var 1,.lt⟩,⟨11,.var 4,.lt⟩]

def kernelComparisons (neg : Bool) (o : ℕ) : List CmpD :=
  [⟨o+8,.const [1],.ge⟩,⟨o+13,.var (o+8),.lt⟩,⟨o+14,.var (o+12),.lt⟩] ++
    if neg then [⟨o+6,.const [1],.ge⟩] else []

def inputDenom (P : Parameters) (b l : ℕ) (k : Fin 4) : Operand :=
  match k.val with
  | 0 => .const (toLimbs b l P.baseM)
  | 1 => .const (toLimbs b l P.baseN)
  | 2 => .var 0
  | _ => .var 1

def inputNumer (k : Fin 4) : Operand :=
  match k.val with
  | 0 => .var 2
  | 1 => .var 0
  | 2 => .var 6
  | _ => .var 7

def inputComparisons (P : Parameters) (b l : ℕ) (k : Fin 4) : List CmpD :=
  [⟨offset k,.const (toLimbs b l (P.U k)),.eq⟩,
   ⟨offset k+1,.const (toLimbs b l (P.V k)),.eq⟩,
   ⟨offset k+2,.const (toLimbs b l (P.Q k)),.eq⟩,
   ⟨offset k+3,inputDenom P b l k,.eq⟩,
   ⟨offset k+4,inputNumer k,.eq⟩,
   ⟨offset k+5,.const (toLimbs b l P.scale),.eq⟩]

def comparisons (P : Parameters) (br : Branch) (b l : ℕ) : List CmpD :=
  headComparisons P br.unitD b l ++
    (List.ofFn fun k : Fin 4 => kernelComparisons (br.neg k) (offset k) ++
      inputComparisons P b l k).flatten

def descriptor (P : Parameters) (br : Branch) (b l : ℕ) : LDesc :=
  compile 72 (equations br) (comparisons P br b l)

@[simp] theorem equations_head (br : Branch) (c : Fin 5) :
    equations br ⟨c.val,by omega⟩=headEquations br.unitD c := by
  simp [equations,c.isLt]

@[simp] theorem equations_kernel (br : Branch) (k : Fin 4) (j : Fin 7) :
    equations br ⟨5+7*k.val+j.val,by omega⟩=
      kernelEquations (br.neg k) (br.imag k) (offset k) j := by
  have h : ¬5+7*k.val+j.val<5 := by omega
  simp only [equations,h,↓reduceDIte]
  have hk : (⟨(5+7*k.val+j.val-5)/7,by omega⟩ : Fin 4)=k := by apply Fin.ext; simp; omega
  simp only [hk]
  congr 1
  apply Fin.ext
  simp
  omega

theorem equations_holds (br : Branch) (b : ℕ) (x : ℕ → ℕ) :
    (∀c,(equations br c).Holds b x) ↔
    (∀c,(headEquations br.unitD c).Holds b x) ∧
      ∀k j,(kernelEquations (br.neg k) (br.imag k) (offset k) j).Holds b x := by
  constructor
  · intro h
    exact ⟨fun c => by simpa using h ⟨c.val,by omega⟩,
      fun k j => by simpa using h ⟨5+7*k.val+j.val,by omega⟩⟩
  · rintro ⟨hh,hk⟩ c
    unfold equations
    split_ifs with hc
    · exact hh ⟨c.val,hc⟩
    · exact hk ⟨(c.val-5)/7,by omega⟩ ⟨(c.val-5)%7,Nat.mod_lt _ (by decide)⟩

theorem kernel_holds_iff (neg imag : Bool) (o b : ℕ) (x : ℕ → ℕ) :
    ((∀j,(kernelEquations neg imag o j).Holds b x) ∧
      ∀q∈kernelComparisons neg o,q.rel.Holds (x q.v) (q.rhs.eval b x)) ↔
    PhaseKernel.Relations neg imag (fun v => x (o+v)) := by
  cases neg <;> cases imag <;>
    simp [Fin.forall_fin_succ,kernelEquations,Equation.Holds,kernelComparisons,
      PhaseKernel.Relations,linearProd,mulProd,zeroProd,ProdD.eval,Operand.eval,
      CmpRel.Holds,limbsVal] <;> tauto

structure Fits (P : Parameters) (b l : ℕ) : Prop where
  two : 2<2^(b*l)
  bound : P.bound<2^(b*l)
  baseM : P.baseM<2^(b*l)
  baseN : P.baseN<2^(b*l)
  twiceM : 2*P.baseM<2^(b*l)
  twiceN : 2*P.baseN<2^(b*l)
  scale : P.scale<2^(b*l)
  U : ∀k,P.U k<2^(b*l)
  V : ∀k,P.V k<2^(b*l)
  Q : ∀k,P.Q k<2^(b*l)

def HeadRelations (P : Parameters) (unitD : Bool) (x : ℕ → ℕ) : Prop :=
  2≤x 0 ∧ 1≤x 1 ∧ 2≤x 2 ∧ x 0≤P.bound ∧ x 0=x 1*x 2 ∧
  x 6=x 0+x 3 ∧ x 7=x 1+x 4 ∧
  x 3<x 0 ∧ x 4<x 1 ∧ x 5<x 0 ∧ 1≤x 3 ∧
  P.baseM≤x 2 ∧ x 2<2*P.baseM ∧ P.baseN≤x 0 ∧ x 0<2*P.baseN ∧
  CoprimeNode.Certificate (x 3) (x 0) (x 8) (x 9) ∧
  if unitD then x 1=1 ∧ x 4=0 ∧ x 10=0 ∧ x 11=0
  else 2≤x 1 ∧ 1≤x 4 ∧ CoprimeNode.Certificate (x 4) (x 1) (x 10) (x 11)

def denomValue (P : Parameters) (k : Fin 4) (x : ℕ → ℕ) : ℕ :=
  match k.val with | 0 => P.baseM | 1 => P.baseN | 2 => x 0 | _ => x 1

def numerValue (k : Fin 4) (x : ℕ → ℕ) : ℕ :=
  match k.val with | 0 => x 2 | 1 => x 0 | 2 => x 6 | _ => x 7

def InputRelations (P : Parameters) (k : Fin 4) (x : ℕ → ℕ) : Prop :=
  x (offset k)=P.U k ∧ x (offset k+1)=P.V k ∧ x (offset k+2)=P.Q k ∧
  x (offset k+3)=denomValue P k x ∧ x (offset k+4)=numerValue k x ∧
  x (offset k+5)=P.scale

def Relations (P : Parameters) (br : Branch) (x : ℕ → ℕ) : Prop :=
  HeadRelations P br.unitD x ∧ ∀k, InputRelations P k x ∧
    PhaseKernel.Relations (br.neg k) (br.imag k) (fun v => x (offset k+v))

theorem head_holds_iff {P : Parameters} {b l : ℕ} (hf : Fits P b l)
    (unitD : Bool) (x : ℕ → ℕ) :
    ((∀c,(headEquations unitD c).Holds b x) ∧
      ∀q∈headComparisons P unitD b l,q.rel.Holds (x q.v) (q.rhs.eval b x)) ↔
      HeadRelations P unitD x := by
  cases unitD <;>
    simp [Fin.forall_fin_succ,headEquations,Equation.Holds,headComparisons,
      HeadRelations,CoprimeNode.Certificate,linearProd,mulProd,zeroProd,
      ProdD.eval,Operand.eval,CmpRel.Holds,limbsVal_toLimbs hf.two,
      limbsVal_toLimbs hf.bound,limbsVal_toLimbs hf.baseM,limbsVal_toLimbs hf.baseN,
      limbsVal_toLimbs hf.twiceM,limbsVal_toLimbs hf.twiceN,
      show limbsVal b [1]=1 by simp [limbsVal],show limbsVal b []=0 by simp [limbsVal],
      ]
  all_goals
    by_cases h4 : x 4=0
    · by_cases h11 : x 11=0
      · simp only [h4,h11,Nat.zero_mul,Nat.mul_zero]
        simp only [Nat.add_zero,Nat.zero_add,Nat.add_comm (x 0*x 9) 1]
        tauto
      · omega
    · omega

theorem input_holds_iff {P : Parameters} {b l : ℕ} (hf : Fits P b l)
    (k : Fin 4) (x : ℕ → ℕ) :
    (∀q∈inputComparisons P b l k,q.rel.Holds (x q.v) (q.rhs.eval b x)) ↔
      InputRelations P k x := by
  fin_cases k <;>
    simp [inputComparisons,InputRelations,inputDenom,inputNumer,denomValue,numerValue,
      CmpRel.Holds,Operand.eval,limbsVal_toLimbs (hf.U _),limbsVal_toLimbs (hf.V _),
      limbsVal_toLimbs (hf.Q _),limbsVal_toLimbs hf.scale,
      limbsVal_toLimbs hf.baseM,limbsVal_toLimbs hf.baseN]

theorem comparisons_holds (P : Parameters) (br : Branch) (b l : ℕ) (F : CmpD → Prop) :
    (∀q∈comparisons P br b l,F q) ↔
    (∀q∈headComparisons P br.unitD b l,F q) ∧
      ∀k,(∀q∈kernelComparisons (br.neg k) (offset k),F q) ∧
        (∀q∈inputComparisons P b l k,F q) := by
  unfold comparisons
  rw [List.forall_mem_append]
  constructor
  · rintro ⟨hh,hk⟩
    refine ⟨hh,fun k => List.forall_mem_append.mp ?_⟩
    intro q hq
    exact hk q (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨k,rfl⟩,hq⟩)
  · rintro ⟨hh,hk⟩
    refine ⟨hh,?_⟩
    intro q hq
    obtain ⟨ls,hls,hq⟩ := List.mem_flatten.mp hq
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hls
    exact List.forall_mem_append.mpr (hk k) q hq

theorem descriptor_sat {P : Parameters} {b l : ℕ} (hf : Fits P b l)
    (br : Branch) (x : ℕ → ℕ) : (descriptor P br b l).D.Sat b x ↔ Relations P br x := by
  rw [descriptor,compile_sat,equations_holds,comparisons_holds]
  constructor
  · rintro ⟨⟨hc,hk⟩,he,hke⟩
    refine ⟨(head_holds_iff hf br.unitD x).1 ⟨he,hc⟩,fun k => ?_⟩
    exact ⟨(input_holds_iff hf k x).1 (hk k).2,
      (kernel_holds_iff (br.neg k) (br.imag k) (offset k) b x).1 ⟨hke k,(hk k).1⟩⟩
  · rintro ⟨hh,hk⟩
    obtain ⟨he,hc⟩ := (head_holds_iff hf br.unitD x).2 hh
    have hks (k : Fin 4) := (kernel_holds_iff (br.neg k) (br.imag k) (offset k) b x).2 (hk k).2
    exact ⟨⟨hc,fun k => ⟨(hks k).2,(input_holds_iff hf k x).2 (hk k).1⟩⟩,
      he,fun k => (hks k).1⟩

end EthFollowup.Primes.FourKernel
