import EthFollowup.Primes.FourKernelDesc

set_option maxHeartbeats 4000000

namespace EthFollowup.Primes.FourKernel
open Finset EthFollowup.ModP EthFollowup.Factoring EthFollowup.ExactHC

theorem offset_bound (k : Fin 4) : offset k+15 ≤ 72 := by
  unfold offset
  omega

theorem head_products_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l) (u : Bool) :
    ∀c i, ((headEquations u c).prod i).u<72 ∧
      ((headEquations u c).prod i).w.OK b l 72 := by
  have h1 : 1<2^b := Nat.one_lt_two_pow (by omega)
  intro c i
  unfold headEquations
  split <;> fin_cases i <;>
    norm_num [Equation.prod,linearProd,mulProd,zeroProd,Operand.OK,hl,h1]

theorem kernel_products_ok {b l o : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l)
    (ho : o+15 ≤ 72) (neg imag : Bool) :
    ∀c i, ((kernelEquations neg imag o c).prod i).u<72 ∧
      ((kernelEquations neg imag o c).prod i).w.OK b l 72 := by
  have h1 : 1<2^b := Nat.one_lt_two_pow (by omega)
  intro c i
  cases neg <;> cases imag <;> unfold kernelEquations <;> split <;> fin_cases i <;>
    norm_num [Equation.prod,linearProd,mulProd,zeroProd,Operand.OK,hl,h1] <;> omega

theorem head_constants_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l) (u : Bool) :
    ∀c, ((headEquations u c).left.length ≤ l ∧ ∀a∈(headEquations u c).left,a<2^b) ∧
      ((headEquations u c).right.length ≤ l ∧ ∀a∈(headEquations u c).right,a<2^b) := by
  have h1 : 1<2^b := Nat.one_lt_two_pow (by omega)
  intro c
  fin_cases c <;> cases u <;> simp [headEquations,hl,h1]

theorem kernel_constants_ok {b l o : ℕ} (neg imag : Bool) :
    ∀c, ((kernelEquations neg imag o c).left.length ≤ l ∧
        ∀a∈(kernelEquations neg imag o c).left,a<2^b) ∧
      ((kernelEquations neg imag o c).right.length ≤ l ∧
        ∀a∈(kernelEquations neg imag o c).right,a<2^b) := by
  intro c
  fin_cases c <;> cases neg <;> simp [kernelEquations]

theorem head_comparisons_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l)
    (P : Parameters) (u : Bool) :
    ∀q∈headComparisons P u b l,q.v<72 ∧ q.rhs.OK b l 72 := by
  have h1 : 1<2^b := Nat.one_lt_two_pow (by omega)
  intro q hq
  cases u <;> simp [headComparisons] at hq <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨by norm_num,toLimbs_OK _ _ _⟩
    | norm_num [Operand.OK,hl,h1]

theorem kernel_comparisons_ok {b l o : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l)
    (ho : o+15 ≤ 72) (neg : Bool) :
    ∀q∈kernelComparisons neg o,q.v<72 ∧ q.rhs.OK b l 72 := by
  have h1 : 1<2^b := Nat.one_lt_two_pow (by omega)
  intro q hq
  cases neg <;> simp [kernelComparisons] at hq <;>
    rcases hq with rfl | rfl | rfl | rfl <;>
    norm_num [Operand.OK,hl,h1] <;> omega

theorem input_comparisons_ok (b l : ℕ) (P : Parameters) (k : Fin 4) :
    ∀q∈inputComparisons P b l k,q.v<72 ∧ q.rhs.OK b l 72 := by
  intro q hq
  fin_cases k <;> simp [inputComparisons,offset,inputDenom,inputNumer] at hq <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨by norm_num,toLimbs_OK _ _ _⟩
    | norm_num [Operand.OK]

theorem comparisons_ok {b l : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l)
    (P : Parameters) (br : Branch) :
    ∀q∈comparisons P br b l,q.v<72 ∧ q.rhs.OK b l 72 := by
  intro q hq
  rcases List.mem_append.mp hq with hh | hk
  · exact head_comparisons_ok hb hl P br.unitD q hh
  · obtain ⟨ls,hls,hq⟩ := List.mem_flatten.mp hk
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hls
    rcases List.mem_append.mp hq with hk | hi
    · exact kernel_comparisons_ok hb hl (offset_bound k) (br.neg k) q hk
    · exact input_comparisons_ok b l P k q hi

/-- The actual full four-kernel descriptor is well formed without numeric Fits
premises: toLimbs truncation affects semantics but never syntactic validity. -/
theorem descriptor_WFB {b l : ℕ} (P : Parameters) (br : Branch) (lk : ℕ → ℕ)
    (hb : 1 ≤ b) (hl : 1 ≤ l) (hl0 : lk 0=l) :
    (descriptor P br b l).WFB b lk := by
  apply compile_WFB (equations br) (comparisons P br b l) lk hl0
  · intro c i
    unfold equations
    split_ifs with hc
    · exact head_products_ok hb hl br.unitD _ i
    · exact kernel_products_ok hb hl (offset_bound _) _ _ _ i
  · intro c
    unfold equations
    split_ifs with hc
    · exact (head_constants_ok hb hl br.unitD _).1
    · exact (kernel_constants_ok _ _ _).1
  · intro c
    unfold equations
    split_ifs with hc
    · exact (head_constants_ok hb hl br.unitD _).2
    · exact (kernel_constants_ok _ _ _).2
  · exact comparisons_ok hb hl P br

theorem comparisons_length_le (P : Parameters) (br : Branch) (b l : ℕ) :
    (comparisons P br b l).length ≤ 58 := by
  simp [comparisons,List.ofFn_succ,headComparisons,kernelComparisons,inputComparisons]
  split_ifs <;> norm_num

theorem descriptor_spread (P : Parameters) (br : Branch) (b l : ℕ) :
    (descriptor P br b l).Spread 132 where
  var := by
    intro v hv
    change v<72 at hv
    change v/132 ≤ 0
    omega
  prod := by
    intro p hp
    have hp' : p<132 := by
      simpa only [descriptor,compile,compiledProducts,List.length_ofFn] using hp
    change p/132 ≤ 0
    omega
  chain := by
    intro c hc
    have hc' : c<33 := by simpa only [descriptor,compile,List.length_ofFn] using hc
    change c/132 ≤ 0
    omega
  cmp := by
    intro q hq
    have hlen := comparisons_length_le P br b l
    change q<(comparisons P br b l).length at hq
    change q/132 ≤ 0
    omega

def actualDesc (P : Parameters) (br : Branch) (n : ℕ) : LDesc :=
  descriptor P br (b n) (kl n 0)

theorem actualDesc_WF (P : Parameters) (br : Branch) (n : ℕ) :
    (actualDesc P br n).WF n :=
  descriptor_WFB P br (kl n) (one_le_b n) (kl_pos n 0) rfl

theorem actualDesc_spread (P : Parameters) (br : Branch) (n : ℕ) :
    (actualDesc P br n).Spread 132 := descriptor_spread P br (b n) (kl n 0)

theorem actualNetwork_communication (P : Parameters) (br : Branch) {n g : ℕ} (hg : 2 ≤ g) :
    ((arithSys n (actualDesc P br n) g hg).net (aLabCode n)).U ≤ 2^19*132*(n+2) := by
  apply arithSys_U_le hg (actualDesc_WF P br n) (actualDesc_spread P br n) (by norm_num)
  simp [actualDesc,descriptor,compile,LDesc.nL]

theorem actualNetwork_is (P : Parameters) (br : Branch) {n g : ℕ} (hg : 2 ≤ g) :
    ((arithSys n (actualDesc P br n) g hg).net (aLabCode n)).Is (PL n 132 g) 1 := by
  apply arithSys_is hg (actualDesc_WF P br n) (actualDesc_spread P br n) (by norm_num)
  simp [actualDesc,descriptor,compile,LDesc.nL]

end EthFollowup.Primes.FourKernel
