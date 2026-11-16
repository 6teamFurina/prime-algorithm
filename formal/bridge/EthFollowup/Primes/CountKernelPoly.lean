/- Polynomial-time, fixed-width readers for the unweighted four-kernel count. -/
import EthFollowup.Primes.CountKernelCountFinal
import EthFollowup.Primes.ArithLPackage
import EthFollowup.Primes.PrimePkgs
import EthFollowup.ModP.SpecHorner

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.CountKernel
open Groundwork EthFollowup.ModP EthFollowup.Factoring

section Poly
variable {α β : Type} [Enc α] [Enc β]

/-- A fixed finite tuple can be assembled by polynomial-time readers. -/
theorem ofFn_polyT {n : ℕ} (f : α → Fin n → β)
    (hf : ∀i,PolyT (fun x => f x i)) : PolyT fun x => List.ofFn (f x) := by
  induction n with
  | zero => simpa using (PolyT.const ([] : List β) : PolyT (fun _ : α => []))
  | succ n ih =>
    simpa only [List.ofFn_succ] using
      PolyT.cons' (hf 0) (ih (fun x i => f x i.succ) (fun i => hf i.succ))

theorem kernel_prod_polyT {neg imag : α → Bool} (hn : PolyT neg) (hi : PolyT imag)
    (o : ℕ) (j : Fin 7) (i : Fin 4) :
    PolyT fun x => (kernelEquations (neg x) (imag x) o j).prod i := by
  fin_cases j <;> fin_cases i <;>
    simp [kernelEquations,Equation.prod,linearProd,mulProd,zeroProd,apply_ite] <;> fun_prop

theorem equations_prod_polyT {br : α → Branch}
    (hn : ∀k,PolyT fun x => (br x).neg k) (hi : ∀k,PolyT fun x => (br x).imag k)
    (c : Fin 33) (i : Fin 4) : PolyT fun x => (equations (br x) c).prod i := by
  by_cases h : c.val<5
  · simp only [equations,h,↓reduceDIte]
    generalize hc : (⟨c.val,h⟩ : Fin 5)=j
    fin_cases j <;> fin_cases i <;>
      simp [headEquations,Equation.prod] <;> exact PolyT.const _
  · simp only [equations,h,↓reduceDIte]
    exact kernel_prod_polyT (hn _) (hi _) _ _ _

theorem equations_left_polyT {br : α → Branch} (c : Fin 33) :
    PolyT fun x => (equations (br x) c).left := by
  have e : ∀br,(equations br c).left=[] := by
    intro br
    unfold equations
    split_ifs <;> rename_i h
    · generalize (⟨c.val,h⟩ : Fin 5)=j
      fin_cases j <;> rfl
    · generalize (⟨(c.val-5)%7,Nat.mod_lt _ (by decide)⟩ : Fin 7)=j
      fin_cases j <;> simp [kernelEquations]; split <;> rfl
  simpa only [e] using (PolyT.const ([] : List ℕ) : PolyT (fun _ : α => []))

theorem equations_right_polyT {br : α → Branch}
    (hu : PolyT fun x => (br x).unitD) (c : Fin 33) :
    PolyT fun x => (equations (br x) c).right := by
  by_cases h : c.val<5
  · simp only [equations,h,↓reduceDIte]
    generalize (⟨c.val,h⟩ : Fin 5)=j
    fin_cases j <;> simp only [headEquations] <;> fun_prop
  · have e : ∀br,(equations br c).right=[] := by
      intro br
      simp only [equations,h,↓reduceDIte]
      generalize (⟨(c.val-5)%7,Nat.mod_lt _ (by decide)⟩ : Fin 7)=j
      fin_cases j <;> simp [kernelEquations]; split <;> rfl
    simpa only [e] using (PolyT.const ([] : List ℕ) : PolyT (fun _ : α => []))

theorem compiledChain_polyT {br : α → Branch}
    (hu : PolyT fun x => (br x).unitD) (c : Fin 33) :
    PolyT fun x => compiledChain (equations (br x)) c := by
  have hl := equations_left_polyT (br := br) c
  have hr := equations_right_polyT hu c
  unfold compiledChain
  fun_prop

theorem headComparisons_polyT {P : α → Parameters} {unitD : α → Bool} {b l : α → ℕ}
    (hb : Unary b) (hl : Unary l) (hu : PolyT unitD)
    (hN : PolyT fun x => (P x).bound) (hM : PolyT fun x => (P x).baseM)
    (hNN : PolyT fun x => (P x).baseN) :
    PolyT fun x => headComparisons (P x) (unitD x) (b x) (l x) := by
  have h2 := toLimbs_polyT hb hl (PolyT.const 2)
  have hn := toLimbs_polyT hb hl hN
  have hm := toLimbs_polyT hb hl hM
  have hnn := toLimbs_polyT hb hl hNN
  have hm2 := toLimbs_polyT hb hl (PolyT.mul (PolyT.const 2) hM)
  have hn2 := toLimbs_polyT hb hl (PolyT.mul (PolyT.const 2) hNN)
  unfold headComparisons
  fun_prop

theorem kernelComparisons_polyT {neg : α → Bool} (hn : PolyT neg) (o : ℕ) :
    PolyT fun x => kernelComparisons (neg x) o := by
  unfold kernelComparisons
  fun_prop

theorem inputComparisons_polyT {P : α → Parameters} {b l : α → ℕ}
    (hb : Unary b) (hl : Unary l)
    (hM : PolyT fun x => (P x).baseM) (hN : PolyT fun x => (P x).baseN)
    (hS : PolyT fun x => (P x).scale)
    (hU : ∀k,PolyT fun x => (P x).U k) (hV : ∀k,PolyT fun x => (P x).V k)
    (hQ : ∀k,PolyT fun x => (P x).Q k) (k : Fin 4) :
    PolyT fun x => inputComparisons (P x) (b x) (l x) k := by
  have hmu := toLimbs_polyT hb hl hM
  have hnu := toLimbs_polyT hb hl hN
  have hs := toLimbs_polyT hb hl hS
  have hu := toLimbs_polyT hb hl (hU k)
  have hv := toLimbs_polyT hb hl (hV k)
  have hq := toLimbs_polyT hb hl (hQ k)
  have hd : PolyT fun x => inputDenom (P x) (b x) (l x) k := by
    fin_cases k <;> simp only [inputDenom] <;> fun_prop
  unfold inputComparisons
  fun_prop

theorem descriptor_polyT {P : α → Parameters} {br : α → Branch} {b l : α → ℕ}
    (hb : Unary b) (hl : Unary l)
    (hbound : PolyT fun x => (P x).bound)
    (hM : PolyT fun x => (P x).baseM) (hN : PolyT fun x => (P x).baseN)
    (hS : PolyT fun x => (P x).scale)
    (hU : ∀k,PolyT fun x => (P x).U k) (hV : ∀k,PolyT fun x => (P x).V k)
    (hQ : ∀k,PolyT fun x => (P x).Q k)
    (hu : PolyT fun x => (br x).unitD)
    (hn : ∀k,PolyT fun x => (br x).neg k) (hi : ∀k,PolyT fun x => (br x).imag k) :
    PolyT fun x => descriptor (P x) (br x) (b x) (l x) := by
  have hp : PolyT fun x => compiledProducts (equations (br x)) :=
    ofFn_polyT _ (fun p => equations_prod_polyT hn hi _ _)
  have hc : PolyT fun x => List.ofFn (compiledChain (equations (br x))) :=
    ofFn_polyT _ (compiledChain_polyT hu)
  have hhead := headComparisons_polyT hb hl hu hbound hM hN
  have hbody : PolyT fun x => List.ofFn fun k : Fin 4 =>
      kernelComparisons ((br x).neg k) (offset k) ++ inputComparisons (P x) (b x) (l x) k :=
    ofFn_polyT _ (fun k => PolyT.append (kernelComparisons_polyT (hn k) _)
      (inputComparisons_polyT hb hl hM hN hS hU hV hQ k))
  have hcmps : PolyT fun x => comparisons (P x) (br x) (b x) (l x) := by
    unfold comparisons
    fun_prop
  unfold descriptor compile
  fun_prop
end Poly

/-- Exactly 24 equal-width entries; the bound is read from the input word. -/
def queryData (P : Parameters) (br : Branch) : List ℕ :=
  [P.baseM,P.baseN,P.scale,
   P.U 0,P.V 0,P.Q 0,P.U 1,P.V 1,P.Q 1,
   P.U 2,P.V 2,P.Q 2,P.U 3,P.V 3,P.Q 3,
   if br.unitD then 1 else 0,
   if br.neg 0 then 1 else 0,if br.neg 1 then 1 else 0,
   if br.neg 2 then 1 else 0,if br.neg 3 then 1 else 0,
   if br.imag 0 then 1 else 0,if br.imag 1 then 1 else 0,
   if br.imag 2 then 1 else 0,if br.imag 3 then 1 else 0]

def query (P : Parameters) (br : Branch) : List Bool := encodeList (queryData P br)

@[simp] theorem queryData_length (P : Parameters) (br : Branch) :
    (queryData P br).length=24 := rfl

def readParameters (w π : List Bool) : Parameters where
  bound := Groundwork.ofWord w
  baseM := rdBlk 24 0 π
  baseN := rdBlk 24 1 π
  scale := rdBlk 24 2 π
  U k := rdBlk 24 (3+3*k.val) π
  V k := rdBlk 24 (4+3*k.val) π
  Q k := rdBlk 24 (5+3*k.val) π

def readBranch (π : List Bool) : Branch where
  unitD := decide (rdBlk 24 15 π=1)
  neg k := decide (rdBlk 24 (16+k.val) π=1)
  imag k := decide (rdBlk 24 (20+k.val) π=1)

theorem rdBlk_query (P : Parameters) (br : Branch) (j : ℕ) (hj : j<24) :
    rdBlk 24 j (query P br)=(queryData P br).getD j 0 :=
  rdBlk_encodeList (show j<(queryData P br).length from hj)

theorem readParameters_query (P : Parameters) (br : Branch) (w : List Bool)
    (hN : Groundwork.ofWord w=P.bound) : readParameters w (query P br)=P := by
  have h := rdBlk_query P br
  cases P
  unfold readParameters
  congr 1
  · rw [h 0 (by decide)]; rfl
  · rw [h 1 (by decide)]; rfl
  · rw [h 2 (by decide)]; rfl
  all_goals funext k; fin_cases k <;> rw [h _ (by decide)] <;> rfl

theorem readBranch_query (P : Parameters) (br : Branch) : readBranch (query P br)=br := by
  have h := rdBlk_query P br
  cases br with
  | mk unitD neg imag =>
    unfold readBranch
    congr 1
    · rw [h 15 (by decide)]
      simp only [queryData,List.getD_cons_succ,List.getD_cons_zero]
      cases unitD <;> rfl
    · funext k
      fin_cases k <;> rw [h _ (by decide)] <;>
        simp only [queryData,List.getD_cons_succ,List.getD_cons_zero]
      all_goals split <;> simp_all
    · funext k
      fin_cases k <;> rw [h _ (by decide)] <;>
        simp only [queryData,List.getD_cons_succ,List.getD_cons_zero]
      all_goals split <;> simp_all

def reader (y : List Bool × List Bool) : LDesc :=
  actualDesc (readParameters y.1 y.2) (readBranch y.2) y.1.length

theorem reader_polyT : PolyT reader := by
  have hblk (i : ℕ) : PolyT fun y : List Bool × List Bool => rdBlk 24 i y.2 :=
    (rdBlk_polyT 24 i).comp (PolyT.snd PolyT.id')
  unfold reader actualDesc
  apply descriptor_polyT (b_unary len_fst_unary) (kl_unary len_fst_unary (PolyT.const 0))
  · exact gofWord_fst_polyT
  · exact hblk 0
  · exact hblk 1
  · exact hblk 2
  · intro k; exact hblk _
  · intro k; exact hblk _
  · intro k; exact hblk _
  · exact PolyT.decide_eq (hblk 15) (PolyT.const 1)
  · intro k; exact PolyT.decide_eq (hblk _) (PolyT.const 1)
  · intro k; exact PolyT.decide_eq (hblk _) (PolyT.const 1)

def arithCountKernel : ArithLSpec where
  nf w := w.length
  nf_le _ := le_rfl
  nf_unary := len_unary
  R w := w.length
  R_le _ := le_rfl
  R_poly := len_unary.poly
  desc := reader
  desc_poly := reader_polyT
  cS := 132
  one_le_cS := by norm_num
  spread y := actualDesc_spread _ _ _
  lev_le y := by simp [reader,actualDesc,descriptor,compile,LDesc.nL]
  wf w π _ := actualDesc_WF _ _ _

/-- One concrete package, with this reader for every input and query word. -/
theorem package_exists :
    ∃pk : CntPackage (2^22*132),
      (∀w π,pk.Q w π=(reader (w,π)).count w.length) ∧
      (∀w,pk.R w=w.length) ∧ (∀w,pk.Ok w) ∧ pk.qb=2^13*132+1 :=
  arithCountKernel.pkg_exists

end EthFollowup.Primes.CountKernel
