import PrimeAlgorithm.IntegerKernelExpansion
import PrimeAlgorithm.CertifiedCoordinateBounds

set_option maxHeartbeats 300000
noncomputable section
namespace PrimeAlgorithm.PrimeQueryExpansion
open Finset CertifiedCauchy CertifiedNumerator CertifiedPrimeSum IntegerKernelExpansion
  EthFollowup.Primes.FourKernel

abbrev NodeChoice (b : ℕ) := Fin (nodeCount b) × Bool
abbrev NodeChoices (b : ℕ) := Fin 4 → NodeChoice b

def parameters (b N jM jN : ℕ) (D : PrimeData) (indices : NodeChoices b) : Parameters where
  bound := N
  baseM := 2^jM
  baseN := 2^jN
  scale := 2^reciprocalBits b
  U k := (D.pole (indices k).1).1.toNat
  V k := (D.pole (indices k).1).2.natAbs
  Q _ := 2^coefficientBits b

def queryBranch {b : ℕ} (unitD : Bool) (indices : NodeChoices b) (σ : Fin 4 → Bool) : Branch :=
  ⟨unitD,σ,fun k => (indices k).2⟩

def binParameters (N jM jN : ℕ) : Parameters :=
  ⟨N,2^jM,2^jN,0,fun _=>0,fun _=>0,fun _=>0⟩

def binBranch (unitD : Bool) : Branch := ⟨unitD,fun _=>false,fun _=>false⟩

def binWitnesses (N jM jN : ℕ) (unitD : Bool) : Finset Base := by
  classical
  exact (Fintype.piFinset fun _ : Fin 5 => range (N+1)).filter
    (BaseRelations (binParameters N jM jN) (binBranch unitD))

theorem mem_binWitnesses {N jM jN : ℕ} {unitD : Bool} {v : Base} :
    v∈binWitnesses N jM jN unitD ↔
      BaseRelations (binParameters N jM jN) (binBranch unitD) v := by
  classical
  simp only [binWitnesses,mem_filter,Fintype.mem_piFinset,mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    obtain ⟨hn,hd,hm,hN,he,hx,hy,_⟩ := h
    change v 0≤N at hN
    intro i
    fin_cases i <;> dsimp <;> nlinarith

theorem baseRelations_parameters (b N jM jN : ℕ) (D : PrimeData) (indices : NodeChoices b)
    (σ : Fin 4 → Bool) (unitD : Bool) (v : Base) :
    BaseRelations (parameters b N jM jN D indices) (queryBranch unitD indices σ) v ↔
      BaseRelations (binParameters N jM jN) (binBranch unitD) v := by
  simp only [BaseRelations,parameters,queryBranch,binParameters,binBranch]
  rfl

def slotData (D : PrimeData) (jM jN : ℕ) (k : Fin 4) : Data :=
  match k.val with
  | 0 => logData D jM
  | 1 => invLogData D jN
  | _ => phaseData D

@[simp] theorem slotData_pole (D : PrimeData) (jM jN : ℕ) (k : Fin 4) :
    (slotData D jM jN k).pole=D.pole := by fin_cases k <;> rfl

def coefficient (b jM jN : ℕ) (D : PrimeData) (k : Fin 4) (a : NodeChoice b)
    (neg : Bool) : GaussianInt :=
  gaussian ((slotData D jM jN k).residue a.1)*componentSign (D.pole a.1) a.2 neg

def horizontalBranch (b N jM jN : ℕ) (D : PrimeData) (k : Fin 4) (a : NodeChoice b)
    (v : Base) : Bool :=
  horizontalSign (coefficientBits b) (D.pole a.1) (kernelNumer v k)
    (kernelDenom (binParameters N jM jN) v k)

def quotient (b N jM jN : ℕ) (D : PrimeData) (k : Fin 4) (a : NodeChoice b)
    (v : Base) : ℕ :=
  componentQuotient (coefficientBits b) (reciprocalBits b) (D.pole a.1)
    (kernelNumer v k) (kernelDenom (binParameters N jM jN) v k) a.2

def queryCoefficient (b jM jN : ℕ) (D : PrimeData) (indices : NodeChoices b)
    (σ : Fin 4 → Bool) : GaussianInt := ∏k,coefficient b jM jN D k (indices k) (σ k)

def queryCount (b N jM jN : ℕ) (D : PrimeData) (indices : NodeChoices b)
    (σ : Fin 4 → Bool) (unitD : Bool) : ℕ :=
  let P := parameters b N jM jN D indices
  let br := queryBranch unitD indices σ
  ∑v∈bases P br,v 0*∏k,kernelQuotient P br v k

def binNumerator (b N jM jN : ℕ) (D : PrimeData) (unitD : Bool) : GaussianInt :=
  ∑v∈binWitnesses N jM jN unitD,(v 0:GaussianInt)*∏k:Fin 4,
    gaussian (numerator (coefficientBits b) (reciprocalBits b) (nodeCount b)
      (slotData D jM jN k) (kernelNumer v k)
      (kernelDenom (binParameters N jM jN) v k))

theorem kernelDenom_parameters (b N jM jN : ℕ) (D : PrimeData) (indices : NodeChoices b)
    (v : Base) (k : Fin 4) :
    kernelDenom (parameters b N jM jN D indices) v k=
      kernelDenom (binParameters N jM jN) v k := by
  simp only [kernelDenom,parameters,binParameters]

theorem kernel_ratio {N jM jN : ℕ} {unitD : Bool} {v : Base}
    (hv : v∈binWitnesses N jM jN unitD) (k : Fin 4) :
    0<kernelDenom (binParameters N jM jN) v k ∧
      (kernelNumer v k:ℝ)/kernelDenom (binParameters N jM jN) v k ∈ Set.Icc 1 2 := by
  obtain ⟨hn,hd,hm,hN,he,hx,hy,hxp,hmlo,hmhi,hnlo,hnhi,_⟩ := mem_binWitnesses.mp hv
  change 2^jM≤v 2 at hmlo
  change v 2<2*2^jM at hmhi
  change 2^jN≤v 0 at hnlo
  change v 0<2*2^jN at hnhi
  have hM : (0:ℝ)<(2^jM:ℕ) := by positivity
  have hN' : (0:ℝ)<(2^jN:ℕ) := by positivity
  have hn' : (0:ℝ)<v 0 := by exact_mod_cast (show 0<v 0 by omega)
  have hd' : (0:ℝ)<v 1 := by exact_mod_cast (show 0<v 1 by omega)
  fin_cases k <;> simp only [kernelDenom,kernelNumer,binParameters]
  · refine ⟨by positivity,?_,?_⟩
    · exact (le_div_iff₀ hM).mpr (by simpa only [one_mul] using (show ((2^jM:ℕ):ℝ)≤v 2 by exact_mod_cast hmlo))
    · exact (div_le_iff₀ hM).mpr (by exact_mod_cast hmhi.le)
  · refine ⟨by positivity,?_,?_⟩
    · exact (le_div_iff₀ hN').mpr (by simpa only [one_mul] using (show ((2^jN:ℕ):ℝ)≤v 0 by exact_mod_cast hnlo))
    · exact (div_le_iff₀ hN').mpr (by exact_mod_cast hnhi.le)
  · refine ⟨by omega,?_,?_⟩
    · apply (le_div_iff₀ hn').mpr
      norm_cast; omega
    · apply (div_le_iff₀ hn').mpr
      norm_cast; omega
  · refine ⟨by omega,?_,?_⟩
    · apply (le_div_iff₀ hd').mpr
      norm_cast; omega
    · apply (div_le_iff₀ hd').mpr
      norm_cast; omega

theorem core_iff {b N jM jN : ℕ} {D : PrimeData} (hD : Certified b D)
    (indices : NodeChoices b) (σ : Fin 4 → Bool) (unitD : Bool) (v : Base) :
    Core (parameters b N jM jN D indices) (queryBranch unitD indices σ) v ↔
      v∈binWitnesses N jM jN unitD ∧
        (fun k => horizontalBranch b N jM jN D k (indices k) v)=σ := by
  have hsign (k : Fin 4) :
      (if σ k then (D.pole (indices k).1).1.toNat*kernelDenom (binParameters N jM jN) v k <
        2^coefficientBits b*kernelNumer v k else
        2^coefficientBits b*kernelNumer v k≤
          (D.pole (indices k).1).1.toNat*kernelDenom (binParameters N jM jN) v k) ↔
      horizontalBranch b N jM jN D k (indices k) v=σ k := by
    unfold horizontalBranch horizontalSign
    cases σ k <;> simp
  constructor
  · rintro ⟨hb,hk⟩
    refine ⟨mem_binWitnesses.mpr ((baseRelations_parameters _ _ _ _ _ _ _ _ _).mp hb),funext fun k=>?_⟩
    apply (hsign k).mp
    have ht := (hk k).1
    cases hσ : σ k <;> simpa only [kernelDenom,parameters,queryBranch,binParameters,hσ,
      Bool.false_eq_true,ite_false,ite_true] using ht
  · rintro ⟨hv,hs⟩
    refine ⟨(baseRelations_parameters _ _ _ _ _ _ _ _ _).mpr (mem_binWitnesses.mp hv),fun k=>⟨?_,?_⟩⟩
    · have h := (hsign k).mpr (congrFun hs k)
      cases hσ : σ k <;> simpa only [kernelDenom,parameters,queryBranch,binParameters,hσ,
        Bool.false_eq_true,ite_false,ite_true] using h
    · obtain ⟨hd,hy⟩ := kernel_ratio hv k
      have hu := CertifiedCoordinateBounds.pole_real_positive hD.phase
        (mem_range.mpr (indices k).1.isLt)
      change 0<(D.pole (indices k).1).1 at hu
      have hp := CertifiedCoordinateBounds.certified_denominator_positive hD.phase
        (mem_range.mpr (indices k).1.isLt) hd hy
      change 0<denominator (coefficientBits b) (D.pole (indices k).1) _ _ at hp
      rw [denominator_eq (coefficientBits b) (D.pole (indices k).1)
        (kernelNumer v k) (kernelDenom (binParameters N jM jN) v k) hu.le] at hp
      simpa only [kernelDenom,parameters,queryBranch,binParameters,
        ←congrFun hs k,horizontalBranch] using hp

theorem queryCount_eq {b N jM jN : ℕ} {D : PrimeData} (hD : Certified b D)
    (indices : NodeChoices b) (σ : Fin 4 → Bool) (unitD : Bool) :
    KernelSumExpansion.count (binWitnesses N jM jN unitD) (fun v=>v 0)
      (fun k v=>quotient b N jM jN D k (indices k) v)
      (fun v k=>horizontalBranch b N jM jN D k (indices k) v) σ =
        queryCount b N jM jN D indices σ unitD := by
  have hs : (binWitnesses N jM jN unitD).filter
      (fun v=>(fun k=>horizontalBranch b N jM jN D k (indices k) v)=σ) =
      bases (parameters b N jM jN D indices) (queryBranch unitD indices σ) := by
    ext v
    rw [mem_filter,mem_bases,core_iff hD]
  unfold KernelSumExpansion.count queryCount
  rw [hs]
  apply sum_congr rfl
  intro v hv
  have hsg := ((core_iff hD indices σ unitD v).mp (mem_bases.mp hv)).2
  apply congrArg (fun a : ℕ=>v 0*a)
  apply prod_congr rfl
  intro k _
  simp only [quotient,componentQuotient,kernelQuotient,kernelDenom,parameters,queryBranch,
    binParameters,←congrFun hsg k,horizontalBranch]

theorem bin_expansion {b N jM jN : ℕ} {D : PrimeData} (hD : Certified b D)
    (unitD : Bool) :
    binNumerator b N jM jN D unitD =
      ∑indices:NodeChoices b,∑σ:Fin 4→Bool,
        queryCoefficient b jM jN D indices σ *
          (queryCount b N jM jN D indices σ unitD:GaussianInt) := by
  have hu (j : ℕ) (hj : j<nodeCount b) : 0≤(D.pole j).1 :=
    (CertifiedCoordinateBounds.pole_real_positive hD.phase (mem_range.mpr hj)).le
  unfold binNumerator
  have hex (v : Base) (k : Fin 4) := numerator_expansion (coefficientBits b) (reciprocalBits b) (nodeCount b)
    (slotData D jM jN k) (kernelNumer v k) (kernelDenom (binParameters N jM jN) v k)
    (by simpa only [slotData_pole] using hu)
  simp_rw [hex]
  simp only [slotData_pole]
  change (∑v∈binWitnesses N jM jN unitD,(v 0:GaussianInt)*∏k:Fin 4,
    ∑a:NodeChoice b,coefficient b jM jN D k a (horizontalBranch b N jM jN D k a v)*
      (quotient b N jM jN D k a v:GaussianInt))=_
  rw [KernelSumExpansion.four_partitioned_expansion]
  apply sum_congr rfl
  intro indices _
  apply sum_congr rfl
  intro σ _
  rw [queryCount_eq hD]
  rfl

theorem bin_term_eq_actual {b N jM jN : ℕ} {D : PrimeData} {unitD : Bool} {v : Base}
    (hv : v∈binWitnesses N jM jN unitD) :
    (v 0:GaussianInt)*∏k:Fin 4,
      gaussian (numerator (coefficientBits b) (reciprocalBits b) (nodeCount b)
        (slotData D jM jN k) (kernelNumer v k)
        (kernelDenom (binParameters N jM jN) v k)) =
      gaussian (v 0 • IntegerPrimeSum.productNumerator b D (v 0) (v 1) (v 3) (v 4)) := by
  obtain ⟨hn,hd,hm,hN,he,hx,hy,hxp,hmlo,hmhi,hnlo,hnhi,_⟩ := mem_binWitnesses.mp hv
  change 2^jM≤v 2 at hmlo
  change v 2<2*2^jM at hmhi
  change 2^jN≤v 0 at hnlo
  change v 0<2*2^jN at hnhi
  have hlogm : Nat.log 2 (v 2)=jM :=
    Nat.log_eq_of_pow_le_of_lt_pow hmlo (by simpa only [pow_succ,Nat.mul_comm] using hmhi)
  have hlogn : Nat.log 2 (v 0)=jN :=
    Nat.log_eq_of_pow_le_of_lt_pow hnlo (by simpa only [pow_succ,Nat.mul_comm] using hnhi)
  have hdiv : v 0/v 1=v 2 := by rw [he,Nat.mul_div_cancel_left _ (by omega)]
  rw [gaussian_nsmul]
  simp only [IntegerPrimeSum.productNumerator,gaussian_multiply,
    IntegerPrimeSum.logNumerator,IntegerPrimeSum.invLogNumerator,IntegerPrimeSum.phaseNumerator,
    hdiv,show ¬v 2<2 by omega,ite_false,hlogm,hlogn,Fin.prod_univ_four]
  norm_num only [slotData,kernelNumer,kernelDenom,binParameters,Fin.val_zero,Fin.val_one,
    Fin.reduceFinMk,Fin.coe_ofNat_eq_mod,Fin.val_natCast, Nat.reduceMod]
  ring

theorem binNumerator_eq_actual (b N jM jN : ℕ) (D : PrimeData) (unitD : Bool) :
    binNumerator b N jM jN D unitD = ∑v∈binWitnesses N jM jN unitD,
      gaussian (v 0 • IntegerPrimeSum.productNumerator b D (v 0) (v 1) (v 3) (v 4)) := by
  unfold binNumerator
  exact sum_congr rfl (fun _ hv=>bin_term_eq_actual hv)

end PrimeAlgorithm.PrimeQueryExpansion
