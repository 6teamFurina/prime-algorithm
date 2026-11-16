import PrimeAlgorithm.PrimeQueryExpansion

set_option maxHeartbeats 1000000
noncomputable section
namespace PrimeAlgorithm.PrimeWitnessReindex
open Finset DoubleRamanujan PrimeQueryExpansion EthFollowup.Primes.FourKernel

abbrev Witness := Σ _n : ℕ, Σ _x : ℕ, Σ _d : ℕ, ℕ

def witnesses (N : ℕ) : Finset Witness :=
  (Icc 2 N).sigma fun n => (unitsBelow n).sigma fun _x =>
    (n.divisors.filter fun d => 2 ≤ n/d).sigma fun d => unitsBelow d

def toBase (w : Witness) : Base := ![w.1,w.2.2.1,w.1/w.2.2.1,w.2.1,w.2.2.2]

def baseWitnesses (N : ℕ) : Finset Base := (witnesses N).image toBase

theorem toBase_injective : Function.Injective toBase := by
  rintro ⟨n,x,d,y⟩ ⟨n',x',d',y'⟩ h
  have hn := congrFun h 0
  have hx := congrFun h 3
  have hd := congrFun h 1
  have hy := congrFun h 4
  change n=n' at hn
  change x=x' at hx
  change d=d' at hd
  change y=y' at hy
  subst n'; subst x'; subst d'; subst y'; rfl

theorem mem_witnesses (N : ℕ) (w : Witness) : w∈witnesses N ↔
    2≤w.1 ∧ w.1≤N ∧ w.2.1∈unitsBelow w.1 ∧
      w.2.2.1∈w.1.divisors ∧ 2≤w.1/w.2.2.1 ∧ w.2.2.2∈unitsBelow w.2.2.1 := by
  simp only [witnesses,mem_sigma,mem_filter,mem_Icc]
  tauto

theorem mem_baseWitnesses {N : ℕ} {v : Base} : v∈baseWitnesses N ↔
    2≤v 0 ∧ v 0≤N ∧ v 3∈unitsBelow (v 0) ∧ v 1∈(v 0).divisors ∧
      2≤v 2 ∧ v 2=v 0/v 1 ∧ v 4∈unitsBelow (v 1) := by
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    simpa [toBase,mem_witnesses] using (mem_witnesses N w).mp hw
  · rintro ⟨hn,hN,hx,hd,hm,he,hy⟩
    refine mem_image.mpr ⟨⟨v 0,v 3,v 1,v 4⟩,?_,?_⟩
    · exact (mem_witnesses _ _).mpr ⟨hn,hN,hx,hd,he ▸ hm,hy⟩
    · funext i
      fin_cases i <;> simp [toBase,he]

theorem original_sum {α : Type*} [AddCommMonoid α] (N : ℕ) (F : Base→α) :
    (∑n∈Icc 2 N,∑x∈unitsBelow n,∑d∈n.divisors.filter (fun d=>2≤n/d),
      ∑y∈unitsBelow d,F ![n,d,n/d,x,y]) = ∑v∈baseWitnesses N,F v := by
  rw [baseWitnesses,sum_image (fun a _ b _ h=>toBase_injective h)]
  simp only [witnesses,sum_sigma,toBase]

theorem unit_positive {x n : ℕ} (hn : 2≤n) (hx : x∈unitsBelow n) : 1≤x := by
  obtain ⟨_,hc⟩ := mem_filter.mp hx
  by_contra h
  have he : x=0 := by omega
  subst x
  simp only [Nat.coprime_zero_left] at hc
  omega

theorem log_bin_iff {n j : ℕ} (hn : 0<n) :
    2^j≤n ∧ n<2*2^j ↔ Nat.log 2 n=j := by
  rw [Nat.log_eq_iff (Or.inr ⟨by decide,hn.ne'⟩)]
  simp [pow_succ,mul_comm]

theorem mem_bin_iff {N jM jN : ℕ} {unitD : Bool} {v : Base} :
    v∈binWitnesses N jM jN unitD ↔
      v∈baseWitnesses N ∧ Nat.log 2 (v 2)=jM ∧ Nat.log 2 (v 0)=jN ∧
        decide (v 1=1)=unitD := by
  rw [mem_binWitnesses,mem_baseWitnesses]
  constructor
  · rintro ⟨hn,hd,hm,hN,he,hx,hy,hxp,hmlo,hmhi,hnlo,hnhi,hxc,hunit⟩
    change 2^jM≤v 2 at hmlo
    change v 2<2*2^jM at hmhi
    change 2^jN≤v 0 at hnlo
    change v 0<2*2^jN at hnhi
    have hdiv : v 0/v 1=v 2 := by rw [he,Nat.mul_div_cancel_left _ (by omega)]
    have hdv : v 1∈(v 0).divisors := Nat.mem_divisors.mpr ⟨⟨v 2,he⟩,by omega⟩
    have hyc : (v 4).Coprime (v 1) := by
      cases unitD
      · exact hunit.2.2
      · simp only [binBranch,Bool.true_eq] at hunit
        simp [hunit.1]
    refine ⟨⟨hn,hN,mem_filter.mpr ⟨mem_range.mpr hx,hxc⟩,hdv,hm,hdiv.symm,
      mem_filter.mpr ⟨mem_range.mpr hy,hyc⟩⟩,
      (log_bin_iff (by omega)).mp ⟨hmlo,hmhi⟩,
      (log_bin_iff (by omega)).mp ⟨hnlo,hnhi⟩,?_⟩
    cases unitD <;> simp only [binBranch,Bool.false_eq_true,if_false,if_true] at hunit ⊢
    · simp [show v 1≠1 by omega]
    · simp [hunit.1]
  · rintro ⟨⟨hn,hN,hx,hd,hm,he,hy⟩,hM,hN',hu⟩
    have hdp := Nat.pos_of_mem_divisors hd
    have hnprod : v 0=v 1*v 2 := by
      rw [he,Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    obtain ⟨hxl,hxc⟩ := mem_filter.mp hx
    obtain ⟨hyl,hyc⟩ := mem_filter.mp hy
    have hxp := unit_positive hn hx
    obtain ⟨hmlo,hmhi⟩ := (log_bin_iff (by omega)).mpr hM
    obtain ⟨hnlo,hnhi⟩ := (log_bin_iff (by omega)).mpr hN'
    refine ⟨hn,hdp,hm,hN,hnprod,mem_range.mp hxl,mem_range.mp hyl,hxp,
      hmlo,hmhi,hnlo,hnhi,hxc,?_⟩
    cases unitD
    · have hne : v 1≠1 := by simpa using hu
      exact ⟨by omega,unit_positive (by omega) hy,hyc⟩
    · have heq : v 1=1 := by simpa using hu
      exact ⟨heq,by have := mem_range.mp hyl; omega⟩

theorem base_log_bounds {N b : ℕ} (hN : N≤2^b) {v : Base}
    (hv : v∈baseWitnesses N) : Nat.log 2 (v 2)≤b ∧ Nat.log 2 (v 0)≤b := by
  obtain ⟨_,hn,_,_,_,he,_⟩ := mem_baseWitnesses.mp hv
  have hn' := Nat.log_mono_right (hn.trans hN) (b:=2)
  rw [Nat.log_pow (by decide)] at hn'
  refine ⟨?_,hn'⟩
  apply le_trans (Nat.log_mono_right (show v 2≤v 0 by rw [he]; exact Nat.div_le_self _ _)) hn'

/-- Each nonzero witness occurs in exactly one pair of logarithmic bins and one
of the two modulus-one branches. -/
theorem sum_bins {α : Type*} [AddCommMonoid α] {N b : ℕ} (hN : N≤2^b)
    (F : Base→α) :
    (∑v∈baseWitnesses N,F v) =
      ∑jM∈range (b+1),∑jN∈range (b+1),∑unitD:Bool,
        ∑v∈binWitnesses N jM jN unitD,F v := by
  let key : Base→ℕ×ℕ×Bool := fun v=>(Nat.log 2 (v 2),Nat.log 2 (v 0),decide (v 1=1))
  have hmap : ∀v∈baseWitnesses N,
      key v∈(range (b+1)).product ((range (b+1)).product (univ : Finset Bool)) := by
    intro v hv
    obtain ⟨hm,hn⟩ := base_log_bounds hN hv
    exact Finset.mem_product.mpr ⟨mem_range.mpr (show Nat.log 2 (v 2)<b+1 by omega),
      Finset.mem_product.mpr ⟨mem_range.mpr (show Nat.log 2 (v 0)<b+1 by omega),mem_univ _⟩⟩
  have hf (j : ℕ×ℕ×Bool) :
      (baseWitnesses N).filter (fun v=>key v=j) = binWitnesses N j.1 j.2.1 j.2.2 := by
    rcases j with ⟨jM,jN,unitD⟩
    ext v
    simp only [mem_filter,mem_bin_iff,key,Prod.mk.injEq]
  rw [←sum_fiberwise_of_maps_to hmap F]
  simp only [hf,Finset.product_eq_sprod,Finset.sum_product]

end PrimeAlgorithm.PrimeWitnessReindex
