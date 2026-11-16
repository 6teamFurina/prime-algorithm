import PrimeAlgorithm.CountQueryPoly
import PrimeAlgorithm.IntegerCountQueryFinal

set_option maxHeartbeats 3000000
namespace PrimeAlgorithm.CountQueryEnumeration
open Groundwork Finset CertifiedCauchy CertifiedPrimeSum CertifiedNumerator
  IntegerKernelExpansion CountQueryExpansion CertifiedGenerator IntegerCountQueryFinal
  EthFollowup.Primes.CountKernel

abbrev Quad (α : Type) := α × α × α × α
abbrev RawIndex := (ℕ × ℕ) × (Bool × (Quad (ℕ × Bool) × Quad Bool))
noncomputable instance : DecidableEq RawIndex := Classical.decEq _

def quadGet {α : Type} (q : Quad α) : Fin 4 → α := ![q.1,q.2.1,q.2.2.1,q.2.2.2]
def quadOf {α : Type} (f : Fin 4 → α) : Quad α := (f 0,f 1,f 2,f 3)

@[simp] theorem quadGet_quadOf {α : Type} (f : Fin 4 → α) : quadGet (quadOf f)=f := by
  funext k; fin_cases k <;> rfl
@[simp] theorem quadOf_quadGet {α : Type} (q : Quad α) : quadOf (quadGet q)=q := by
  rcases q with ⟨a,b,c,d⟩; rfl

@[simp] theorem product_mem {α β : Type} (l : List α) (r : List β) (q : α × β) :
    q∈l.product r ↔ q.1∈l ∧ q.2∈r := by
  rcases q with ⟨a,b⟩
  exact List.mem_product

@[simp] theorem product_length {α β : Type} (l : List α) (r : List β) :
    (l.product r).length=l.length*r.length := List.length_product l r

def quadList {α : Type} (l : List α) : List (Quad α) := l.product (l.product (l.product l))
def nodeList (b : ℕ) : List (ℕ × Bool) := (List.range (nodeCount b)).product [false,true]
def enumerate (b : ℕ) : List RawIndex :=
  ((List.range (b+1)).product (List.range (b+1))).product
    ([false,true].product ((quadList (nodeList b)).product (quadList [false,true])))

def encodeIndex {b : ℕ} (q : QueryIndex b) : RawIndex :=
  ((q.1.val,q.2.1.val),(q.2.2.1,
    (quadOf (fun k => ((q.2.2.2.1 k).1.val,(q.2.2.2.1 k).2)),quadOf q.2.2.2.2)))

def Valid (b : ℕ) (q : RawIndex) : Prop :=
  q.1.1<b+1 ∧ q.1.2<b+1 ∧ ∀k,(quadGet q.2.2.1 k).1<nodeCount b

@[simp] theorem mem_quadList {α : Type} (q : Quad α) (l : List α) :
    q∈quadList l ↔ ∀k,quadGet q k∈l := by
  rcases q with ⟨a,b,c,d⟩
  simp [quadList,List.mem_product,Fin.forall_fin_succ,quadGet]

@[simp] theorem mem_nodeList (b : ℕ) (q : ℕ × Bool) : q∈nodeList b ↔ q.1<nodeCount b := by
  rcases q with ⟨n,u⟩
  cases u <;> simp [nodeList]

theorem mem_enumerate (b : ℕ) (q : RawIndex) : q∈enumerate b ↔ Valid b q := by
  rcases q with ⟨⟨jm,jn⟩,u,ns,ss⟩
  have hu : u∈[false,true] := by cases u <;> simp
  have hs : ss∈quadList [false,true] := by
    rw [mem_quadList]
    intro k; cases quadGet ss k <;> simp
  simp [enumerate,hu,hs,Valid,and_assoc]

def decodeIndex {b : ℕ} (q : RawIndex) (h : Valid b q) : QueryIndex b :=
  (⟨q.1.1,h.1⟩,⟨q.1.2,h.2.1⟩,q.2.1,
    (fun k => (⟨(quadGet q.2.2.1 k).1,h.2.2 k⟩,(quadGet q.2.2.1 k).2)),quadGet q.2.2.2)

@[simp] theorem encodeIndex_valid {b : ℕ} (q : QueryIndex b) : Valid b (encodeIndex q) := by
  refine ⟨q.1.isLt,q.2.1.isLt,?_⟩
  intro k
  simpa [encodeIndex] using (q.2.2.2.1 k).1.isLt

@[simp] theorem encode_decode {b : ℕ} (q : RawIndex) (h : Valid b q) :
    encodeIndex (decodeIndex q h)=q := by
  simp [encodeIndex,decodeIndex]

@[simp] theorem decode_encode {b : ℕ} (q : QueryIndex b) :
    decodeIndex (encodeIndex q) (encodeIndex_valid q)=q := by
  rcases q with ⟨jm,jn,u,ns,ss⟩
  simp only [decodeIndex,encodeIndex,quadGet_quadOf]

theorem encodeIndex_injective (b : ℕ) : Function.Injective (@encodeIndex b) := by
  intro q r h
  have he : decodeIndex (encodeIndex q) (encodeIndex_valid q)=
      decodeIndex (encodeIndex r) (encodeIndex_valid r) := by congr 1
  simpa using he

theorem enumerate_nodup (b : ℕ) : (enumerate b).Nodup := by
  have hb : ([false,true]:List Bool).Nodup := by decide
  have hn : (nodeList b).Nodup := List.nodup_range.product hb
  have hq {α : Type} (l : List α) (h : l.Nodup) : (quadList l).Nodup :=
    h.product (h.product (h.product h))
  exact (List.nodup_range.product List.nodup_range).product
    (hb.product ((hq _ hn).product (hq _ hb)))

theorem enumerate_toFinset (b : ℕ) :
    (enumerate b).toFinset=univ.image (@encodeIndex b) := by
  ext q
  simp only [List.mem_toFinset,mem_enumerate,mem_image,mem_univ,true_and]
  constructor
  · intro h; exact ⟨decodeIndex q h,encode_decode q h⟩
  · rintro ⟨q,rfl⟩; exact encodeIndex_valid q

/-- Enumeration agrees exactly with the mathematical query index, without multiplicities. -/
theorem sum_enumerate {A : Type} [AddCommMonoid A] (b : ℕ) (f : RawIndex → A) :
    ((enumerate b).map f).sum=∑q:QueryIndex b,f (encodeIndex q) := by
  rw [←List.sum_toFinset _ (enumerate_nodup b),enumerate_toFinset]
  exact sum_image (fun _ _ _ _ h => encodeIndex_injective b h)

theorem enumerate_length (b : ℕ) :
    (enumerate b).length=(b+1)^2*2*(2*nodeCount b)^4*16 := by
  simp only [enumerate,quadList,nodeList,product_length,List.length_range,
    List.length_cons,List.length_nil]
  ring

section Poly
variable {α β γ : Type} [Enc α] [Enc β] [Enc γ]

theorem product_polyT {l : α → List β} {r : α → List γ} (hl : PolyT l) (hr : PolyT r) :
    PolyT fun x => (l x).product (r x) := by
  have hfst : PolyT fun p : α × β => p.1 := PolyT.fst PolyT.id'
  have hg : PolyT fun p : (α × β) × γ => (p.1.2,p.2) := by fun_prop
  exact PolyT.flatMap (f := fun x a => (r x).map fun c => (a,c))
    (PolyT.map (f := fun p c => (p.2,c)) hg (hr.comp hfst)) hl

theorem quadList_polyT {l : α → List β} (hl : PolyT l) : PolyT fun x => quadList (l x) :=
  product_polyT hl (product_polyT hl (product_polyT hl hl))

theorem quadGet_polyT {q : α → Quad β} (hq : PolyT q) (k : Fin 4) :
    PolyT fun x => quadGet (q x) k := by
  fin_cases k
  · exact PolyT.fst hq
  · exact PolyT.fst (PolyT.snd hq)
  · exact PolyT.fst (PolyT.snd (PolyT.snd hq))
  · exact PolyT.snd (PolyT.snd (PolyT.snd hq))

theorem enumerate_polyT {b : α → ℕ} (hb : Unary b) : PolyT fun x => enumerate (b x) := by
  have hbin := PolyT.range (hb.add (Unary.const 1))
  have hn : PolyT fun x => nodeList (b x) :=
    product_polyT (PolyT.range (nodeCount_unary hb)) (PolyT.const [false,true])
  exact product_polyT (product_polyT hbin hbin)
    (product_polyT (PolyT.const [false,true])
      (product_polyT (quadList_polyT hn) (quadList_polyT (PolyT.const [false,true]))))
end Poly

def rawParameters (b N : ℕ) (q : RawIndex) : Parameters where
  bound := N
  baseM := 2^(min q.1.1 b)
  baseN := 2^(min q.1.2 b)
  scale := 2^reciprocalBits b
  U k := (pole b (quadGet q.2.2.1 k).1).1.toNat
  V k := (pole b (quadGet q.2.2.1 k).1).2.natAbs
  Q _ := 2^coefficientBits b

def rawBranch (q : RawIndex) : Branch :=
  ⟨q.2.1,quadGet q.2.2.2,fun k => (quadGet q.2.2.1 k).2⟩

def wordQuery (b N : ℕ) (q : RawIndex) : List Bool := query (rawParameters b N q) (rawBranch q)

def residuePair (b : ℕ) (q : RawIndex) (k : Fin 4) : GaussianIntPair :=
  match k.val with
  | 0 => logResidue b (min q.1.1 b) (quadGet q.2.2.1 k).1
  | 1 => invLogResidue b (min q.1.2 b) (quadGet q.2.2.1 k).1
  | _ => phaseResidue b (quadGet q.2.2.1 k).1

def signPair (z : GaussianIntPair) (imag neg : Bool) : GaussianIntPair :=
  if imag then (0,if z.2<0 then 1 else -1) else (if neg then -1 else 1,0)

def coefficientPair (b : ℕ) (q : RawIndex) (k : Fin 4) : GaussianIntPair :=
  multiply (residuePair b q k) (signPair (pole b (quadGet q.2.2.1 k).1)
    (quadGet q.2.2.1 k).2 (quadGet q.2.2.2 k))

def integerWeight (b : ℕ) (q : RawIndex) : ℤ :=
  -(multiply (multiply (multiply (coefficientPair b q 0) (coefficientPair b q 1))
    (coefficientPair b q 2)) (coefficientPair b q 3)).1

def items (b N : ℕ) : List (List Bool × ℤ) :=
  (enumerate b).map fun q => (wordQuery b N q,integerWeight b q)

@[simp] theorem rawParameters_encodeIndex (b N : ℕ) (q : QueryIndex b) :
    rawParameters b N (encodeIndex q)=queryParameters b N (generate b) q := by
  have hM : q.1.val≤b := by omega
  have hN : q.2.1.val≤b := by omega
  simp [rawParameters,encodeIndex,queryParameters,parameters,generate,
    Nat.min_eq_left hM,Nat.min_eq_left hN]

@[simp] theorem rawBranch_encodeIndex (b : ℕ) (q : QueryIndex b) :
    rawBranch (encodeIndex q)=branch b q := by
  simp [rawBranch,encodeIndex,branch,queryBranch]

@[simp] theorem wordQuery_encodeIndex (b N : ℕ) (q : QueryIndex b) :
    wordQuery b N (encodeIndex q)=query (queryParameters b N (generate b) q) (branch b q) := by
  simp [wordQuery]

@[simp] theorem gaussian_signPair (z : GaussianIntPair) (imag neg : Bool) :
    gaussian (signPair z imag neg)=componentSign z imag neg := by
  cases imag <;> cases neg <;> simp [signPair,componentSign,gaussian] <;> rfl

@[simp] theorem residuePair_encodeIndex (b : ℕ) (q : QueryIndex b) (k : Fin 4) :
    residuePair b (encodeIndex q) k=(slotData (generate b) q.1 q.2.1 k).residue (q.2.2.2.1 k).1 := by
  have hM : q.1.val≤b := by omega
  have hN : q.2.1.val≤b := by omega
  fin_cases k <;> simp [residuePair,encodeIndex,slotData,generate,logData,invLogData,phaseData,
    quadOf,quadGet,Nat.min_eq_left hM,Nat.min_eq_left hN]

@[simp] theorem coefficientPair_encodeIndex (b : ℕ) (q : QueryIndex b) (k : Fin 4) :
    gaussian (coefficientPair b (encodeIndex q) k)=
      CountQueryExpansion.coefficient b q.1 q.2.1 (generate b) k (q.2.2.2.1 k) (q.2.2.2.2 k) := by
  unfold coefficientPair
  rw [gaussian_multiply,residuePair_encodeIndex,gaussian_signPair]
  simp only [CountQueryExpansion.coefficient,encodeIndex,quadGet_quadOf,generate]

@[simp] theorem integerWeight_encodeIndex (b : ℕ) (q : QueryIndex b) :
    integerWeight b (encodeIndex q)=(IntegerCountQueryFinal.coefficient b (generate b) q).re := by
  have he : gaussian (multiply (multiply (multiply (coefficientPair b (encodeIndex q) 0)
      (coefficientPair b (encodeIndex q) 1)) (coefficientPair b (encodeIndex q) 2))
      (coefficientPair b (encodeIndex q) 3)) =
      queryCoefficient b q.1 q.2.1 (generate b) q.2.2.2.1 q.2.2.2.2 := by
    simp only [gaussian_multiply,coefficientPair_encodeIndex,queryCoefficient,Fin.prod_univ_four]
  have hr := congrArg Zsqrtd.re he
  simpa only [integerWeight,IntegerCountQueryFinal.coefficient,Zsqrtd.re_neg,gaussian] using congrArg Neg.neg hr

section ProgramPoly
variable {α : Type} [Enc α]

theorem min_unary {n b : α → ℕ} (hn : PolyT n) (hb : Unary b) :
    Unary (fun x => min (n x) (b x)) :=
  Unary.of_le hb (PolyT.min' hn hb.poly) (fun _ => Nat.min_le_right _ _)

theorem wordQuery_polyT {b N : α → ℕ} {q : α → RawIndex}
    (hb : Unary b) (hq : PolyT q) : PolyT fun x => wordQuery (b x) (N x) (q x) := by
  have hn (k : Fin 4) : PolyT fun x => quadGet (q x).2.2.1 k :=
    quadGet_polyT (PolyT.fst (PolyT.snd (PolyT.snd hq))) k
  have hs (k : Fin 4) : PolyT fun x => quadGet (q x).2.2.2 k :=
    quadGet_polyT (PolyT.snd (PolyT.snd (PolyT.snd hq))) k
  have hp (k : Fin 4) := pole_polyT hb (PolyT.fst (hn k))
  apply query_polyT
  · exact PolyT.two_pow (min_unary (PolyT.fst (PolyT.fst hq)) hb)
  · exact PolyT.two_pow (min_unary (PolyT.snd (PolyT.fst hq)) hb)
  · exact PolyT.two_pow (CountQueryPoly.reciprocalBits_unary hb)
  · intro k; exact PolyT.toNat (PolyT.fst (hp k))
  · intro k; exact PolyT.natAbs (PolyT.snd (hp k))
  · intro k; exact PolyT.two_pow (coefficientBits_unary hb)
  · exact PolyT.fst (PolyT.snd hq)
  · exact hs
  · intro k; exact PolyT.snd (hn k)

theorem multiply_polyT {z w : α → GaussianIntPair} (hz : PolyT z) (hw : PolyT w) :
    PolyT fun x => multiply (z x) (w x) := by unfold multiply; fun_prop

theorem signPair_polyT {z : α → GaussianIntPair} {i n : α → Bool}
    (hz : PolyT z) (hi : PolyT i) (hn : PolyT n) :
    PolyT fun x => signPair (z x) (i x) (n x) := by unfold signPair; fun_prop

theorem residuePair_polyT {b : α → ℕ} {q : α → RawIndex}
    (hb : Unary b) (hq : PolyT q) (k : Fin 4) :
    PolyT fun x => residuePair (b x) (q x) k := by
  have hn (k : Fin 4) : PolyT fun x => (quadGet (q x).2.2.1 k).1 :=
    PolyT.fst (quadGet_polyT (PolyT.fst (PolyT.snd (PolyT.snd hq))) k)
  have hm := (min_unary (PolyT.fst (PolyT.fst hq)) hb).poly
  have hnn := (min_unary (PolyT.snd (PolyT.fst hq)) hb).poly
  fin_cases k
  · exact logResidue_polyT hb hm (hn _)
  · exact invLogResidue_polyT hb hnn (hn _)
  · exact phaseResidue_polyT hb (hn _)
  · exact phaseResidue_polyT hb (hn _)

theorem coefficientPair_polyT {b : α → ℕ} {q : α → RawIndex}
    (hb : Unary b) (hq : PolyT q) (k : Fin 4) :
    PolyT fun x => coefficientPair (b x) (q x) k := by
  have hn := quadGet_polyT (PolyT.fst (PolyT.snd (PolyT.snd hq))) k
  have hs := quadGet_polyT (PolyT.snd (PolyT.snd (PolyT.snd hq))) k
  exact multiply_polyT (residuePair_polyT hb hq k)
    (signPair_polyT (pole_polyT hb (PolyT.fst hn)) (PolyT.snd hn) hs)

theorem integerWeight_polyT {b : α → ℕ} {q : α → RawIndex}
    (hb : Unary b) (hq : PolyT q) : PolyT fun x => integerWeight (b x) (q x) := by
  exact PolyT.negZ (PolyT.fst (multiply_polyT
    (multiply_polyT (multiply_polyT (coefficientPair_polyT hb hq 0)
      (coefficientPair_polyT hb hq 1)) (coefficientPair_polyT hb hq 2))
    (coefficientPair_polyT hb hq 3)))

theorem items_polyT {b N : α → ℕ} (hb : Unary b) (hN : PolyT N) :
    PolyT fun x => items (b x) (N x) := by
  have hf : PolyT fun x : α × RawIndex => x.1 := PolyT.fst PolyT.id'
  have hq : PolyT fun x : α × RawIndex => x.2 := PolyT.snd PolyT.id'
  exact PolyT.map (f := fun x q => (wordQuery (b x) (N x) q,integerWeight (b x) q))
    (PolyT.prodMk (wordQuery_polyT (hb.comp hf) hq)
      (integerWeight_polyT (hb.comp hf) hq)) (enumerate_polyT hb)
end ProgramPoly

theorem items_length (b N : ℕ) :
    (items b N).length=(b+1)^2*2*(2*nodeCount b)^4*16 := by
  simp [items,enumerate_length]

/-- Every emitted item is exactly one mathematical query and its signed integer coefficient. -/
theorem mem_items (b N : ℕ) (item : List Bool × ℤ) :
    item∈items b N ↔ ∃q:QueryIndex b,
      item=(query (queryParameters b N (generate b) q) (branch b q),
        (IntegerCountQueryFinal.coefficient b (generate b) q).re) := by
  constructor
  · intro h
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
    have hv := (mem_enumerate b r).mp hr
    let q := decodeIndex r hv
    have he : encodeIndex q=r := encode_decode r hv
    refine ⟨q,?_⟩
    rw [←he,wordQuery_encodeIndex,integerWeight_encodeIndex]
  · rintro ⟨q,rfl⟩
    apply List.mem_map.mpr
    exact ⟨encodeIndex q,(mem_enumerate b _).mpr (encodeIndex_valid q),by simp⟩

private def realPart : GaussianInt →+ ℤ where
  toFun := Zsqrtd.re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Summing the computed integer weights against correct oracle counts gives the
real coordinate of the exact integer prime-counting numerator. -/
theorem sum_items_count (b N : ℕ) (C : List Bool → ℕ)
    (hC : ∀q:QueryIndex b,
      C (query (queryParameters b N (generate b) q) (branch b q))=
        IntegerCountQueryFinal.count b N (generate b) q) :
    ((items b N).map (fun item => item.2*(C item.1:ℤ))).sum=
      (queryNumerator b N (generate b)).re := by
  unfold items
  rw [List.map_map,sum_enumerate]
  simp only [Function.comp_apply,wordQuery_encodeIndex,integerWeight_encodeIndex]
  change _ = realPart (∑q:QueryIndex b,
    IntegerCountQueryFinal.coefficient b (generate b) q*
      (IntegerCountQueryFinal.count b N (generate b) q:GaussianInt))
  rw [map_sum]
  apply sum_congr rfl
  intro q _
  rw [hC q]
  change _ = (IntegerCountQueryFinal.coefficient b (generate b) q*
    (IntegerCountQueryFinal.count b N (generate b) q:GaussianInt)).re
  simp [Zsqrtd.re_mul,Zsqrtd.re_natCast,Zsqrtd.im_natCast]

/-- One package supplies every item emitted by the actual generator. Both the
query-length obligation and the complete weighted sum are discharged. -/
theorem items_package_exists :
    ∃pk : EthFollowup.ModP.CntPackage (2^22*132),
      (∀w,pk.R w=w.length) ∧ (∀w,pk.Ok w) ∧
      ∀(b N : ℕ) (w : List Bool), Certified b (generate b) → N≤2^b →
        Groundwork.ofWord w=N → b≤w.length+1 →
        (∀item∈items b N,item.1.length≤pk.R (EthFollowup.Primes.LinearPadding.pad w)) ∧
        ((items b N).map (fun item => item.2*(pk.Q (EthFollowup.Primes.LinearPadding.pad w) item.1:ℤ))).sum=
          (queryNumerator b N (generate b)).re := by
  obtain ⟨pk,hR,hOk,hqb,hquery⟩ := CountQueryBounds.concrete_package_exists
  refine ⟨pk,hR,hOk,?_⟩
  intro b N w hD hN hw hb
  have hq (q : QueryIndex b) :
      (query (queryParameters b N (generate b) q) (branch b q)).length≤
        pk.R (EthFollowup.Primes.LinearPadding.pad w) ∧
      pk.Q (EthFollowup.Primes.LinearPadding.pad w) (query (queryParameters b N (generate b) q) (branch b q))=
        IntegerCountQueryFinal.count b N (generate b) q := by
    exact hquery b N q.1 q.2.1 (generate b) hD hN (by omega) (by omega)
      q.2.2.2.1 q.2.2.2.2 q.2.2.1 w hw hb
  constructor
  · intro item hi
    obtain ⟨q,rfl⟩ := (mem_items b N item).mp hi
    exact (hq q).1
  · exact sum_items_count b N (pk.Q (EthFollowup.Primes.LinearPadding.pad w)) (fun q => (hq q).2)

end PrimeAlgorithm.CountQueryEnumeration
