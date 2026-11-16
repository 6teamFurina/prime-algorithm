/- A concrete fixed-slot compiler for constant-arity arithmetic equations. -/
import EthFollowup.Primes.PhaseKernelInstance
import EthFollowup.Primes.CoprimeResidue

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.CountKernel
open Finset EthFollowup.ModP

/-- Two product slots and one constant on each side. Zero slots are still real
    products, each owned by precisely one chain. -/
structure Equation where
  p0 : ProdD
  p1 : ProdD
  p2 : ProdD
  p3 : ProdD
  left : List ℕ := []
  right : List ℕ := []
  deriving Inhabited, DecidableEq, Repr

def Equation.prod (e : Equation) (i : Fin 4) : ProdD :=
  match i.val with
  | 0 => e.p0
  | 1 => e.p1
  | 2 => e.p2
  | _ => e.p3

def Equation.Holds (e : Equation) (b : ℕ) (x : ℕ → ℕ) : Prop :=
  e.p0.eval b x + e.p1.eval b x + limbsVal b e.left =
    e.p2.eval b x + e.p3.eval b x + limbsVal b e.right

def compiledProducts {m : ℕ} (es : Fin m → Equation) : List ProdD :=
  List.ofFn fun p : Fin (m*4) =>
    (es ⟨p.val/4,by omega⟩).prod ⟨p.val%4,Nat.mod_lt _ (by decide)⟩

def compiledChain {m : ℕ} (es : Fin m → Equation) (c : Fin m) : ChainD :=
  ⟨[⟨1,.prod (4*c.val)⟩,⟨1,.prod (4*c.val+1)⟩,⟨1,.const (es c).left⟩],
   [⟨1,.prod (4*c.val+2)⟩,⟨1,.prod (4*c.val+3)⟩,⟨1,.const (es c).right⟩]⟩

def compile {m : ℕ} (nV : ℕ) (es : Fin m → Equation) (cs : List CmpD) : LDesc where
  D := ⟨nV,[],compiledProducts es,List.ofFn (compiledChain es),cs⟩
  lev := []
  levC := []

@[simp] theorem getD_ofFn_lt {α : Type} [Inhabited α] {m : ℕ} (f : Fin m → α)
    (i : ℕ) (hi : i< m) : (List.ofFn f).getD i default = f ⟨i,hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

@[simp] theorem compiledProducts_get {m : ℕ} (es : Fin m → Equation)
    (c : Fin m) (i : Fin 4) :
    (compiledProducts es).getD (4*c.val+i.val) default = (es c).prod i := by
  unfold compiledProducts
  rw [getD_ofFn_lt _ _ (by omega)]
  congr 2
  · apply Fin.ext
    change (4*c.val+i.val)/4=c.val
    omega
  · change (4*c.val+i.val)%4=i.val
    omega

theorem compiledChain_holds {m : ℕ} (es : Fin m → Equation) (c : Fin m)
    (b : ℕ) (x : ℕ → ℕ) :
    sideVal b (compiledProducts es) x (compiledChain es c).lhs =
      sideVal b (compiledProducts es) x (compiledChain es c).rhs ↔
    (es c).Holds b x := by
  simp only [compiledChain,sideVal,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Term.coeff,Src.eval,one_mul,add_zero]
  have h0 := compiledProducts_get es c (0:Fin 4)
  have h1 := compiledProducts_get es c (1:Fin 4)
  have h2 := compiledProducts_get es c (2:Fin 4)
  have h3 := compiledProducts_get es c (3:Fin 4)
  simp only [show (0:Fin 4).val=0 from rfl, show (1:Fin 4).val=1 from rfl,
    show (2:Fin 4).val=2 from rfl,show (3:Fin 4).val=3 from rfl,add_zero] at h0 h1 h2 h3
  rw [h0,h1,h2,h3]
  change ((es c).p0.eval b x+((es c).p1.eval b x+limbsVal b (es c).left) =
    (es c).p2.eval b x+((es c).p3.eval b x+limbsVal b (es c).right)) ↔ _
  simp [Equation.Holds,Nat.add_assoc]

theorem compile_sat {m : ℕ} (nV : ℕ) (es : Fin m → Equation)
    (cs : List CmpD) (b : ℕ) (x : ℕ → ℕ) :
    (compile nV es cs).D.Sat b x ↔
      (∀q∈cs,q.rel.Holds (x q.v) (q.rhs.eval b x)) ∧ ∀c, (es c).Holds b x := by
  simp only [compile,Desc.Sat,patMatch,List.getD_nil,List.length_nil,Nat.not_lt_zero,
    IsEmpty.forall_iff,true_implies,List.mem_ofFn,forall_exists_index,forall_eq_apply_imp_iff,
    compiledChain_holds]
  simp [compiledChain_holds]

theorem compiledChain_hasProd {m : ℕ} (es : Fin m → Equation) (c : Fin m) (p : ℕ) :
    (compiledChain es c).HasProd p ↔ 4*c.val≤p ∧ p<4*c.val+4 := by
  simp [compiledChain,ChainD.HasProd]
  omega

/-- Well-formedness of the actual compiled grammar. No product has two owners. -/
theorem compile_WFB {m nV b l : ℕ} (es : Fin m → Equation) (cs : List CmpD)
    (lk : ℕ → ℕ) (hl0 : lk 0=l)
    (hp : ∀c i,((es c).prod i).u < nV ∧ ((es c).prod i).w.OK b l nV)
    (hleft : ∀c,(es c).left.length≤l ∧ ∀a∈(es c).left,a<2^b)
    (hright : ∀c,(es c).right.length≤l ∧ ∀a∈(es c).right,a<2^b)
    (hcs : ∀q∈cs,q.v<nV ∧ q.rhs.OK b l nV) :
    (compile nV es cs).WFB b lk where
  pat_len := by intro v hv; simp [compile]
  prod_ok := by
    intro p hp'
    have hpm : p< m*4 := by simpa [compile,compiledProducts] using hp'
    let c : Fin m := ⟨p/4,by omega⟩
    let i : Fin 4 := ⟨p%4,Nat.mod_lt _ (by decide)⟩
    have he : p=4*c.val+i.val := by dsimp [c,i]; omega
    have hpci := hp c i
    have hg : (compiledProducts es).getD p default=(es c).prod i := by
      rw [he]; exact compiledProducts_get es c i
    refine ⟨?_,?_,?_,?_⟩
    · change ((compiledProducts es).getD p default).u<nV
      rw [hg]
      exact hpci.1
    · simp [compile,LDesc.lp,LDesc.lc,LDesc.lv]
    · change (compile nV es cs).OpOK b lk 0 ((compiledProducts es).getD p default).w
      rw [hg]
      cases hw : ((es c).prod i).w with
      | var v => simpa [LDesc.OpOK,LDesc.lv,compile,Operand.OK,hw] using hpci.2
      | const xs => simpa [LDesc.OpOK,Operand.OK,hw,hl0] using hpci.2
    · have hcc : c.val<(compile nV es cs).D.chains.length := by simpa [compile] using c.isLt
      have hc : ((compile nV es cs).D.chains.getD c.val default).HasProd p := by
        change ((List.ofFn (compiledChain es)).getD c.val default).HasProd p
        rw [getD_ofFn_lt _ _ c.isLt,compiledChain_hasProd]
        dsimp [c]
        omega
      exact lt_of_le_of_lt (Desc.chainOf_spec hcc hc).1 hcc
  term_ok := by
    intro c hc tm htm
    have hcm : c< m := by simpa [compile] using hc
    change tm ∈ ((List.ofFn (compiledChain es)).getD c default).lhs ++
      ((List.ofFn (compiledChain es)).getD c default).rhs at htm
    rw [getD_ofFn_lt _ _ hcm] at htm
    simp [compiledChain] at htm
    rcases htm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [LDesc.SrcOK,compile,LDesc.lc,compiledProducts,hl0]
    all_goals first | omega | exact hleft ⟨c,hcm⟩ | exact hright ⟨c,hcm⟩
  coeff_le := by
    intro ch hch
    change ch ∈ List.ofFn (compiledChain es) at hch
    obtain ⟨c,rfl⟩ := List.mem_ofFn.mp hch
    norm_num [compiledChain]
  prod_once := by
    intro c hc c' hc' p hp hp'
    have hcm : c< m := by simpa [compile] using hc
    have hcm' : c'< m := by simpa [compile] using hc'
    change ((List.ofFn (compiledChain es)).getD c default).HasProd p at hp
    change ((List.ofFn (compiledChain es)).getD c' default).HasProd p at hp'
    rw [getD_ofFn_lt _ _ hcm,compiledChain_hasProd] at hp
    rw [getD_ofFn_lt _ _ hcm',compiledChain_hasProd] at hp'
    change 4*c≤p ∧ p<4*c+4 at hp
    change 4*c'≤p ∧ p<4*c'+4 at hp'
    omega
  cmp_ok := by
    intro q hq
    change q<cs.length at hq
    have hm : cs.getD q default ∈ cs := by
      rw [List.getD_eq_getElem _ _ hq]
      exact List.getElem_mem hq
    obtain ⟨hv,ho⟩ := hcs _ hm
    refine ⟨hv,?_⟩
    change (compile nV es cs).CmpOK b lk 0 (cs.getD q default).rhs
    cases he : (cs.getD q default).rhs with
    | var v =>
      rw [he] at ho
      simpa [LDesc.CmpOK,Operand.OK,compile,LDesc.lv] using ho
    | const xs =>
      rw [he] at ho
      simpa [LDesc.CmpOK,Operand.OK,hl0] using ho

end EthFollowup.Primes.CountKernel
