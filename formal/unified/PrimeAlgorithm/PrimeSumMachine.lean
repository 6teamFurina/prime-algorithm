import PrimeAlgorithm.PrimeMachineInput
import PrimeAlgorithm.PrimeQueryFinish
import PrimeAlgorithm.PrimeQueryEnumeration
import EthFollowup.ModP.BatchCollect

set_option maxHeartbeats 300000
noncomputable section
namespace PrimeAlgorithm.PrimeSumMachine
open Groundwork EthFollowup.ModP EthFollowup.Primes
  PrimeMachineInput CertifiedGenerator

def rawItems (w : List Bool) : List BatchCollect.Item :=
  PrimeQueryEnumeration.items (precision w) (ofWord w)

def items (w : List Bool) : List BatchCollect.Item :=
  (rawItems w).filter fun q=>decide (q.1.length≤w.length)

def finish : List Bool × List ℕ → List Bool := PrimeQueryFinish.finish precision items

def spec : NatBatchQuerySpec := BatchCollect.spec items finish

theorem rawItems_polyT : PolyT rawItems :=
  PrimeQueryEnumeration.items_polyT precision_unary (by fun_prop)

theorem items_polyT : PolyT items := by
  apply PolyT.filter (f:=fun (w : List Bool) (q : BatchCollect.Item)=>decide (q.1.length≤w.length))
  · fun_prop
  · exact rawItems_polyT

theorem finish_polyT : PolyT finish := PrimeQueryFinish.finish_polyT precision_unary items_polyT

@[simp] theorem rawItems_pad (w : List Bool) : rawItems (LinearPadding.pad w)=rawItems w := by
  simp only [rawItems,precision_pad,LinearPadding.pad_value]

theorem items_pad (w : List Bool)
    (hl : ∀q∈rawItems w,q.1.length≤(LinearPadding.pad w).length) :
    items (LinearPadding.pad w)=rawItems w := by
  unfold items
  rw [rawItems_pad]
  apply List.filter_eq_self.mpr
  intro q hq
  exact decide_eq_true (hl q hq)

theorem valid {c₀ : ℕ} (pk : CntPackage c₀)
    (hR : ∀w,pk.R w=w.length) (hOk : ∀w,pk.Ok w)
    (w : List Bool) (i : ℕ) (hi : i<(items w).length) :
    pk.Ok w ∧ (((items w).getD i ([],0)).1).length≤pk.R w := by
  refine ⟨hOk w,?_⟩
  rw [hR,List.getD_eq_getElem (items w) ([],0) hi]
  have hm : (items w)[i]∈items w := List.getElem_mem hi
  have hh := (List.mem_filter.mp hm).2
  exact of_decide_eq_true hh

theorem bounds {c₀ : ℕ} (pk : CntPackage c₀)
    (hR : ∀w,pk.R w=w.length) (hOk : ∀w,pk.Ok w) :
    ∃a,NatBatchQuery.Bounds pk spec a :=
  BatchCollect.bounds pk items_polyT finish_polyT (valid pk hR hOk)

theorem answer_pad {c₀ : ℕ} (pk : CntPackage c₀) (w : List Bool)
    (hlen : ∀q∈rawItems w,q.1.length≤(LinearPadding.pad w).length)
    (hsum : ((rawItems w).map fun q=>q.2*(pk.Q (LinearPadding.pad w) q.1:ℤ)).sum=
      (IntegerPrimeQueryFinal.queryNumerator (precision w) (ofWord w) (generate (precision w))).re) :
    NatBatchQuery.answer pk spec (LinearPadding.pad w)=Nat.bits (primeSum (ofWord w)) := by
  rw [show spec=BatchCollect.spec items finish from rfl,BatchCollect.answer_eq]
  change PrimeQueryFinish.finish precision items _=_
  apply PrimeQueryFinish.finish_queries_eq_primeSum _ _ (generate (precision w)) (ofWord w)
  · rw [PrimeQueryFinish.dot_map_count,items_pad w hlen,precision_pad]
    exact hsum
  · rw [precision_pad]
    exact value_bound w
  · rw [precision_pad]
    exact generate_certified _

theorem TM_of_package {c₀ : ℕ} (pk : CntPackage c₀)
    (hR : ∀w,pk.R w=w.length) (hOk : ∀w,pk.Ok w)
    (hlen : ∀w q,q∈rawItems w → q.1.length≤(LinearPadding.pad w).length)
    (hsum : ∀w,((rawItems w).map fun q=>q.2*(pk.Q (LinearPadding.pad w) q.1:ℤ)).sum=
      (IntegerPrimeQueryFinal.queryNumerator (precision w) (ofWord w) (generate (precision w))).re) :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i,Finite (M.tm.Γ i)) ∧
      ∀w : List Bool, GraphProblems.Outputs M w (Nat.bits (primeSum (ofWord w)))
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ := by
  obtain ⟨a,hb⟩ := bounds pk hR hOk
  have hf : PolyT spec.finish := by
    dsimp only [spec,BatchCollect.spec]
    exact finish_polyT
  obtain ⟨M,C,hfinite,hrun⟩ := NatBatchQuery.machine_TM_linear_input pk spec
    (BatchCollect.rounds_polyT (finish:=finish) items_polyT)
    (BatchCollect.initial_polyT (items:=items) (finish:=finish))
    (BatchCollect.query_polyT (finish:=finish) items_polyT)
    (BatchCollect.update_polyT (items:=items) (finish:=finish)) hf hb
    LinearPadding.pad LinearPadding.pad_polyT (L:=2049)
    (fun w=>(LinearPadding.pad_length_bounds w).1)
    (fun w=>(LinearPadding.pad_length_bounds w).2)
  refine ⟨M,C,hfinite,fun w=>?_⟩
  have h := hrun w
  rw [answer_pad pk w (hlen w) (hsum w)] at h
  exact h

/-- One finite-alphabet Turing machine computes the exact sum of primes for
every binary input. Its complete running time, including coefficient generation,
query enumeration and integer reconstruction, has the stated bound. -/
theorem primeSum_TM :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i,Finite (M.tm.Γ i)) ∧
      ∀w : List Bool, GraphProblems.Outputs M w (Nat.bits (primeSum (ofWord w)))
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ := by
  obtain ⟨pk,hR,hOk,hsem⟩ := PrimeQueryEnumeration.items_package_exists
  apply TM_of_package pk hR hOk
  · intro w q hq
    have h := (hsem (precision w) (ofWord w) w (generate_certified _)
      (value_bound w) rfl (precision_le w)).1 q hq
    rwa [hR] at h
  · intro w
    exact (hsem (precision w) (ofWord w) w (generate_certified _)
      (value_bound w) rfl (precision_le w)).2

/-- Natural-number form of the same theorem, with the actual binary input length. -/
theorem primeSum_TM_all_inputs :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i,Finite (M.tm.Γ i)) ∧
      ∀N : ℕ, GraphProblems.Outputs M (Nat.bits N) (Nat.bits (primeSum N))
        ⌊(C:ℝ)*2^((C:ℝ)*(Nat.bits N).length/
          Real.sqrt (Real.logb 2 ((Nat.bits N).length+2)))⌋₊ := by
  obtain ⟨M,C,hfinite,hrun⟩ := primeSum_TM
  refine ⟨M,C,hfinite,fun N=>?_⟩
  have h := hrun (Nat.bits N)
  have hv : ofWord (Nat.bits N)=N := by rw [bits_eq_encodeNat,gofWord_encodeNat]
  rwa [hv] at h

end PrimeAlgorithm.PrimeSumMachine
