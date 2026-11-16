import PrimeAlgorithm.PrimeQueryExpansion
import EthFollowup.Primes.FourKernelQuery
import EthFollowup.Primes.LinearPadding

set_option maxHeartbeats 1000000
noncomputable section
namespace PrimeAlgorithm.PrimeQueryBounds
open Finset Groundwork CertifiedCauchy CertifiedPrimeSum CertifiedCoordinateBounds
  PrimeQueryExpansion EthFollowup.Primes EthFollowup.Primes.FourKernel
  EthFollowup.ModP

private theorem toNat_le_natAbs (z : ℤ) : z.toNat≤z.natAbs := by cases z <;> simp

theorem power_lt_inputBits {b j : ℕ} (hj : j≤b) : 2^j<2^inputBits b := by
  apply Nat.pow_lt_pow_right (by decide)
  unfold inputBits
  omega

theorem doubled_power_le_inputBits {b j : ℕ} (hj : j≤b) :
    2*2^j≤2^inputBits b := by
  rw [←pow_succ']
  apply Nat.pow_le_pow_right (by decide)
  unfold inputBits
  omega

theorem scale_lt_inputBits (b : ℕ) : 2^reciprocalBits b<2^inputBits b := by
  apply Nat.pow_lt_pow_right (by decide)
  unfold reciprocalBits Cauchy.dyadicBits inputBits
  omega

theorem coefficientScale_lt_inputBits (b : ℕ) : 2^coefficientBits b<2^inputBits b := by
  apply Nat.pow_lt_pow_right (by decide)
  unfold coefficientBits Cauchy.dyadicBits inputBits
  omega

theorem parameters_U_lt {b : ℕ} {D : PrimeData} (hD : Certified b D)
    (N jM jN : ℕ) (indices : NodeChoices b) (k : Fin 4) :
    (parameters b N jM jN D indices).U k<2^inputBits b :=
  (toNat_le_natAbs _).trans_lt
    (pole_bit_bound hD.phase (mem_range.mpr (indices k).1.isLt)).1

theorem parameters_V_lt {b : ℕ} {D : PrimeData} (hD : Certified b D)
    (N jM jN : ℕ) (indices : NodeChoices b) (k : Fin 4) :
    (parameters b N jM jN D indices).V k<2^inputBits b :=
  (pole_bit_bound hD.phase (mem_range.mpr (indices k).1.isLt)).2

/-- All true arithmetic inputs of this algorithm have the proved linear bit bound. -/
theorem parameters_bitBounds {b N jM jN : ℕ} {D : PrimeData}
    (hD : Certified b D) (hN : N≤2^b) (hM : jM≤b) (hNN : jN≤b)
    (indices : NodeChoices b) :
    BitBounds (parameters b N jM jN D indices) (inputBits b) where
  two := by
    have := doubled_power_le_inputBits (b:=b) (j:=0) (by omega)
    simpa using this
  bound := (Nat.mul_le_mul_left 2 hN).trans (doubled_power_le_inputBits le_rfl)
  baseM := doubled_power_le_inputBits hM
  baseN := doubled_power_le_inputBits hNN
  scale := (scale_lt_inputBits b).le
  U k := (parameters_U_lt hD N jM jN indices k).le
  V k := (parameters_V_lt hD N jM jN indices k).le
  Q _ := (coefficientScale_lt_inputBits b).le

private theorem queryData_lt {P : Parameters} {br : Branch} {B : ℕ}
    (h1 : 1<2^B) (hM : P.baseM<2^B) (hN : P.baseN<2^B) (hS : P.scale<2^B)
    (hU : ∀k,P.U k<2^B) (hV : ∀k,P.V k<2^B) (hQ : ∀k,P.Q k<2^B) :
    ∀x∈queryData P br,x<2^B := by
  have hf (v : Bool) : (if v then 1 else 0)<2^B := by cases v <;> simp_all
  simp only [queryData,List.forall_mem_cons,List.forall_mem_nil]
  exact ⟨hM,hN,hS,hU 0,hV 0,hQ 0,hU 1,hV 1,hQ 1,hU 2,hV 2,hQ 2,hU 3,hV 3,hQ 3,
    hf _,hf _,hf _,hf _,hf _,hf _,hf _,hf _,hf _,by simp⟩

theorem actual_queryData_lt {b N jM jN : ℕ} {D : PrimeData}
    (hD : Certified b D) (hM : jM≤b) (hN : jN≤b)
    (indices : NodeChoices b) (σ : Fin 4 → Bool) (unitD : Bool) :
    ∀x∈queryData (parameters b N jM jN D indices) (queryBranch unitD indices σ),
      x<2^inputBits b := by
  apply queryData_lt
  · have := power_lt_inputBits (b:=b) (j:=0) (by omega)
    simpa using this
  · exact power_lt_inputBits hM
  · exact power_lt_inputBits hN
  · exact scale_lt_inputBits b
  · exact parameters_U_lt hD N jM jN indices
  · exact parameters_V_lt hD N jM jN indices
  · intro k; exact coefficientScale_lt_inputBits b

/-- The actual 24-entry query fits the fixed linear padding. -/
theorem padded_query_length {b N jM jN : ℕ} {D : PrimeData}
    (hD : Certified b D) (hM : jM≤b) (hN : jN≤b)
    (indices : NodeChoices b) (σ : Fin 4 → Bool) (unitD : Bool)
    (w : List Bool) (hb : b≤w.length+1) :
    (query (parameters b N jM jN D indices) (queryBranch unitD indices σ)).length≤
      (LinearPadding.pad w).length :=
  LinearPadding.parameter_query_fits hb _ (queryData_length _ _)
    (actual_queryData_lt hD hM hN indices σ unitD)

/-- This padded description counts exactly the concrete query of the prime-sum expansion. -/
theorem padded_reader_query_count {b N jM jN : ℕ} {D : PrimeData}
    (hD : Certified b D) (hN : N≤2^b) (hM : jM≤b) (hNN : jN≤b)
    (indices : NodeChoices b) (σ : Fin 4 → Bool) (unitD : Bool)
    (w : List Bool) (hw : Groundwork.ofWord w=N) (hb : b≤w.length+1) :
    (reader (LinearPadding.pad w,
      query (parameters b N jM jN D indices) (queryBranch unitD indices σ))).count
        (LinearPadding.pad w).length = queryCount b N jM jN D indices σ unitD := by
  apply reader_query_count
  · exact (LinearPadding.pad_value w).trans hw
  · exact parameters_bitBounds hD hN hM hNN indices
  · exact LinearPadding.box_width_fits hb

/-- One fixed package implements every certified prime-sum query, including its length obligation. -/
theorem concrete_package_exists :
    ∃pk : CntPackage (2^22*132),
      (∀w,pk.R w=w.length) ∧ (∀w,pk.Ok w) ∧ pk.qb=2^13*132+1 ∧
      ∀(b N jM jN : ℕ) (D : PrimeData), Certified b D → N≤2^b → jM≤b → jN≤b →
      ∀(indices : NodeChoices b) (σ : Fin 4 → Bool) (unitD : Bool)
        (w : List Bool), Groundwork.ofWord w=N → b≤w.length+1 →
        let π := query (parameters b N jM jN D indices) (queryBranch unitD indices σ)
        π.length≤pk.R (LinearPadding.pad w) ∧
          pk.Q (LinearPadding.pad w) π=queryCount b N jM jN D indices σ unitD := by
  obtain ⟨pk,hQ,hR,hOk,hqb⟩ := package_exists
  refine ⟨pk,hR,hOk,hqb,?_⟩
  intro b N jM jN D hD hN hM hNN indices σ unitD w hw hb
  dsimp only
  constructor
  · rw [hR]
    exact padded_query_length hD hM hNN indices σ unitD w hb
  · rw [hQ]
    exact padded_reader_query_count hD hN hM hNN indices σ unitD w hw hb

end PrimeAlgorithm.PrimeQueryBounds
