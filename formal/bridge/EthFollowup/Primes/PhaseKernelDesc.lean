/-
A constant-arity Cauchy reciprocal kernel in the actual ArithL grammar.
Inputs U,V,Q,d,t,S are nonnegative; sign `neg` specifies Ud<Qt.
Auxiliary variables are uniquely determined except the quotient weight witness.
-/
import EthFollowup.Primes.PhaseQuotientDesc

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace EthFollowup.Primes.PhaseKernel

open Finset EthFollowup.ModP

def products (imag : Bool) : List ProdD :=
  [⟨0,.var 3⟩, ⟨2,.var 4⟩, ⟨6,.const [1]⟩,
   ⟨7,.const [1]⟩, ⟨1,.var 3⟩,
   ⟨8,.const [1]⟩, ⟨6,.var 6⟩, ⟨7,.var 7⟩,
   ⟨9,.const [1]⟩, ⟨2,.var 3⟩,
   ⟨10,.const [1]⟩, ⟨9,.var (if imag then 7 else 6)⟩,
   ⟨11,.const [1]⟩, ⟨5,.var 10⟩,
   ⟨11,.const [1]⟩, ⟨8,.var 12⟩, ⟨13,.const [1]⟩]

def chains (neg : Bool) : List ChainD :=
  [(if neg then ⟨[⟨1,.prod 0⟩,⟨1,.prod 2⟩],[⟨1,.prod 1⟩]⟩
    else ⟨[⟨1,.prod 0⟩],[⟨1,.prod 1⟩,⟨1,.prod 2⟩]⟩),
   ⟨[⟨1,.prod 3⟩],[⟨1,.prod 4⟩]⟩,
   ⟨[⟨1,.prod 5⟩],[⟨1,.prod 6⟩,⟨1,.prod 7⟩]⟩,
   ⟨[⟨1,.prod 8⟩],[⟨1,.prod 9⟩]⟩,
   ⟨[⟨1,.prod 10⟩],[⟨1,.prod 11⟩]⟩,
   ⟨[⟨1,.prod 12⟩],[⟨1,.prod 13⟩]⟩,
   ⟨[⟨1,.prod 14⟩],[⟨1,.prod 15⟩,⟨1,.prod 16⟩]⟩]

def comparisons (neg : Bool) : List CmpD :=
  [⟨8,.const [1],.ge⟩, ⟨13,.var 8,.lt⟩, ⟨14,.var 12,.lt⟩] ++
    if neg then [⟨6,.const [1],.ge⟩] else []

def mkDesc (neg imag : Bool) (cs : List CmpD) : LDesc where
  D := {nV:=15,pat:=[],prods:=products imag,chains:=chains neg,cmps:=cs}
  lev := []
  levC := []

def pinnedDesc (neg imag : Bool) (b l U V Q d t S : ℕ) : LDesc :=
  mkDesc neg imag (comparisons neg ++
    [⟨0,.const (toLimbs b l U),.eq⟩, ⟨1,.const (toLimbs b l V),.eq⟩,
     ⟨2,.const (toLimbs b l Q),.eq⟩, ⟨3,.const (toLimbs b l d),.eq⟩,
     ⟨4,.const (toLimbs b l t),.eq⟩, ⟨5,.const (toLimbs b l S),.eq⟩])

/-- Fixed-arity arithmetic equations, including the disjoint sign split. -/
def Relations (neg imag : Bool) (x : ℕ → ℕ) : Prop :=
  (if neg then x 0*x 3+x 6=x 2*x 4 ∧ 1≤x 6 else x 0*x 3=x 2*x 4+x 6) ∧
  x 7=x 1*x 3 ∧ x 8=x 6*x 6+x 7*x 7 ∧ x 9=x 2*x 3 ∧
  x 10=x 9*(if imag then x 7 else x 6) ∧ x 11=x 5*x 10 ∧
  x 11=x 8*x 12+x 13 ∧ 1≤x 8 ∧ x 13<x 8 ∧ x 14<x 12

theorem pinnedDesc_sat {neg imag : Bool} {b l U V Q d t S : ℕ}
    (hU : U<2^(b*l)) (hV : V<2^(b*l)) (hQ : Q<2^(b*l))
    (hd : d<2^(b*l)) (ht : t<2^(b*l)) (hS : S<2^(b*l)) (x : ℕ → ℕ) :
    (pinnedDesc neg imag b l U V Q d t S).D.Sat b x ↔
      x 0=U ∧ x 1=V ∧ x 2=Q ∧ x 3=d ∧ x 4=t ∧ x 5=S ∧ Relations neg imag x := by
  cases neg <;> cases imag <;>
    simp [pinnedDesc,mkDesc,comparisons,Relations,Desc.Sat,patMatch,CmpRel.Holds,
      Operand.eval,limbsVal_toLimbs hU,limbsVal_toLimbs hV,limbsVal_toLimbs hQ,
      limbsVal_toLimbs hd,limbsVal_toLimbs ht,limbsVal_toLimbs hS,
      products,chains,sideVal,Src.eval,ProdD.eval,
      show limbsVal b [1]=1 by simp [limbsVal]] <;> tauto

theorem mkDesc_WFB {b l : ℕ} (neg imag : Bool) (cs : List CmpD) (lk : ℕ → ℕ)
    (hb : 1≤b) (hl : 1≤l) (hl0 : lk 0=l)
    (hcs : ∀ q ∈ cs, q.v<15 ∧ q.rhs.OK b l 15) :
    (mkDesc neg imag cs).WFB b lk where
  pat_len := by intro v hv; simp [mkDesc]
  prod_ok := by
    intro p hp
    have hp' : p<17 := by simpa [mkDesc,products] using hp
    have h1 : 1<2^b := Nat.one_lt_two_pow (by omega)
    interval_cases p <;> cases neg <;> cases imag <;>
      norm_num [mkDesc,products,chains,LDesc.OpOK,LDesc.lv,LDesc.lp,LDesc.lc,
        Desc.chainOf,ChainD.HasProd,hl0,hl,h1] <;> decide
  term_ok := by
    intro c hc tm hm
    have hc' : c<7 := by simpa [mkDesc,chains] using hc
    interval_cases c <;> cases neg <;> cases imag <;>
      simp [mkDesc,chains] at hm <;>
      rcases hm with rfl | rfl | rfl <;>
      norm_num [LDesc.SrcOK,mkDesc,products]
  coeff_le := by
    intro ch hch
    cases neg <;> simp [mkDesc,chains] at hch <;>
      rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  prod_once := by
    intro c hc c' hc' p hp hp'
    have hca : c<7 := by simpa [mkDesc,chains] using hc
    have hcb : c'<7 := by simpa [mkDesc,chains] using hc'
    interval_cases c <;> interval_cases c' <;> cases neg <;>
      simp [mkDesc,chains,ChainD.HasProd] at hp hp' ⊢ <;> omega
  cmp_ok := by
    intro q hq
    change q<cs.length at hq
    have hm : cs.getD q default ∈ cs := by
      rw [List.getD_eq_getElem _ _ hq]
      exact List.getElem_mem hq
    obtain ⟨hv,ho⟩ := hcs _ hm
    refine ⟨hv,?_⟩
    change (mkDesc neg imag cs).CmpOK b lk 0 (cs.getD q default).rhs
    cases he : (cs.getD q default).rhs with
    | var v =>
      rw [he] at ho
      simpa [LDesc.CmpOK,Operand.OK,mkDesc,LDesc.lv] using ho
    | const xs =>
      rw [he] at ho
      simpa [LDesc.CmpOK,Operand.OK,hl0] using ho

theorem comparisons_ok {b l : ℕ} (neg : Bool) (hb : 1≤b) (hl : 1≤l) :
    ∀ q ∈ comparisons neg, q.v<15 ∧ q.rhs.OK b l 15 := by
  intro q hq
  have h1 : 1<2^b := Nat.one_lt_two_pow (by omega)
  cases neg <;> simp [comparisons] at hq <;>
    rcases hq with rfl | rfl | rfl | rfl <;>
    norm_num [Operand.OK,hl,h1]

theorem pinnedDesc_WFB {b l U V Q d t S : ℕ} (neg imag : Bool) (lk : ℕ → ℕ)
    (hb : 1≤b) (hl : 1≤l) (hl0 : lk 0=l) :
    (pinnedDesc neg imag b l U V Q d t S).WFB b lk := by
  apply mkDesc_WFB neg imag _ lk hb hl hl0
  intro q hq
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with hq | rfl | rfl | rfl | rfl | rfl | rfl
  · exact comparisons_ok neg hb hl _ hq
  · exact ⟨by norm_num, toLimbs_OK b l U⟩
  · exact ⟨by norm_num, toLimbs_OK b l V⟩
  · exact ⟨by norm_num, toLimbs_OK b l Q⟩
  · exact ⟨by norm_num, toLimbs_OK b l d⟩
  · exact ⟨by norm_num, toLimbs_OK b l t⟩
  · exact ⟨by norm_num, toLimbs_OK b l S⟩

theorem pinnedDesc_spread (neg imag : Bool) (b l U V Q d t S : ℕ) :
    (pinnedDesc neg imag b l U V Q d t S).Spread 17 where
  var := by intro v hv; simp [pinnedDesc,mkDesc,LDesc.lv] at *; omega
  prod := by intro p hp; simp [pinnedDesc,mkDesc,products,LDesc.lp,LDesc.lc] at *; omega
  chain := by intro c hc; simp [pinnedDesc,mkDesc,chains,LDesc.lc] at *; omega
  cmp := by
    intro q hq
    cases neg <;> simp [pinnedDesc,mkDesc,comparisons,LDesc.lq,LDesc.lv] at * <;> omega

/-- The free-input kernel is a real descriptor available for descriptor composition. -/
def nodeDesc (neg imag : Bool) : LDesc := mkDesc neg imag (comparisons neg)

theorem nodeDesc_sat (neg imag : Bool) (b : ℕ) (x : ℕ → ℕ) :
    (nodeDesc neg imag).D.Sat b x ↔ Relations neg imag x := by
  cases neg <;> cases imag <;>
    simp [nodeDesc,mkDesc,comparisons,Relations,Desc.Sat,patMatch,CmpRel.Holds,
      Operand.eval,products,chains,sideVal,Src.eval,ProdD.eval,
      show limbsVal b [1]=1 by simp [limbsVal]] <;> tauto

theorem nodeDesc_WFB {b l : ℕ} (neg imag : Bool) (lk : ℕ → ℕ)
    (hb : 1≤b) (hl : 1≤l) (hl0 : lk 0=l) : (nodeDesc neg imag).WFB b lk :=
  mkDesc_WFB neg imag (comparisons neg) lk hb hl hl0 (comparisons_ok neg hb hl)

theorem nodeDesc_spread (neg imag : Bool) : (nodeDesc neg imag).Spread 17 where
  var := by intro v hv; simp [nodeDesc,mkDesc,LDesc.lv] at *; omega
  prod := by intro p hp; simp [nodeDesc,mkDesc,products,LDesc.lp,LDesc.lc] at *; omega
  chain := by intro c hc; simp [nodeDesc,mkDesc,chains,LDesc.lc] at *; omega
  cmp := by
    intro q hq
    cases neg <;> simp [nodeDesc,mkDesc,comparisons,LDesc.lq,LDesc.lv] at * <;> omega

open EthFollowup.Factoring EthFollowup.ExactHC

def actualDesc (neg imag : Bool) (n U V Q d t S : ℕ) : LDesc :=
  pinnedDesc neg imag (b n) (kl n 0) U V Q d t S

theorem actualDesc_WF (neg imag : Bool) (n U V Q d t S : ℕ) :
    (actualDesc neg imag n U V Q d t S).WF n :=
  pinnedDesc_WFB neg imag (kl n) (one_le_b n) (kl_pos n 0) rfl

theorem actualDesc_spread (neg imag : Bool) (n U V Q d t S : ℕ) :
    (actualDesc neg imag n U V Q d t S).Spread 17 :=
  pinnedDesc_spread neg imag (b n) (kl n 0) U V Q d t S

/-- The real kernel network satisfies the established arithmetic engine's conditions. -/
theorem actualNetwork_is (neg imag : Bool) {n g U V Q d t S : ℕ} (hg : 2≤g) :
    ((arithSys n (actualDesc neg imag n U V Q d t S) g hg).net (aLabCode n)).Is
      (WeightedNetworkBounds.P n (actualDesc neg imag n U V Q d t S) g) 1 :=
  WeightedNetworkBounds.arithSys_is hg (actualDesc_WF neg imag n U V Q d t S)

end EthFollowup.Primes.PhaseKernel
