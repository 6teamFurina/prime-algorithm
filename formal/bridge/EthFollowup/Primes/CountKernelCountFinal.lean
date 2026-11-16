/- Exact count of the assembled arithmetic descriptor, including all shared inputs. -/
import EthFollowup.Primes.CountKernelCount
import EthFollowup.Primes.CountKernelCanonical
import EthFollowup.Primes.CountKernelWF

set_option maxHeartbeats 3000000
noncomputable section
namespace EthFollowup.Primes.CountKernel
open Finset EthFollowup.ModP

theorem core_base_bound {P : Parameters} {br : Branch} {v : Base}
    (hc : Core P br v) : ∀i,v i≤P.bound := by
  obtain ⟨hn,hd,hm,hN,he,hx,hy,_⟩ := hc.1
  intro i
  fin_cases i <;> dsimp <;> nlinarith

def bases (P : Parameters) (br : Branch) : Finset Base := by
  classical
  exact (Fintype.piFinset fun _ : Fin 5 => range (P.bound+1)).filter (Core P br)

theorem mem_bases {P : Parameters} {br : Branch} {v : Base} :
    v∈bases P br ↔ Core P br v := by
  classical
  simp only [bases,mem_filter,Fintype.mem_piFinset,mem_range]
  constructor
  · exact And.right
  · intro hc
    exact ⟨fun i => Nat.lt_succ_of_le (core_base_bound hc i),hc⟩

def weightLimit (P : Parameters) (br : Branch) (v : Base) : Fin 5 → ℕ :=
  Fin.cons 1 (kernelQuotient P br v)

def weightSet (P : Parameters) (br : Branch) (v : Base) : Finset Weights :=
  Fintype.piFinset fun i => range (weightLimit P br v i)

theorem mem_weightSet {P : Parameters} {br : Branch} {v : Base} {w : Weights} :
    w∈weightSet P br v ↔ WeightBounds P br v w := by
  simp [weightSet,weightLimit,WeightBounds,Fin.forall_fin_succ]

theorem card_weightSet (P : Parameters) (br : Branch) (v : Base) :
    (weightSet P br v).card=∏k,kernelQuotient P br v k := by
  rw [weightSet,Fintype.card_piFinset]
  simp only [card_range,Fin.prod_univ_succ,weightLimit,Fin.cons_zero,Fin.cons_succ,one_mul]

def indices (P : Parameters) (br : Branch) : Finset (Σ _ : Base,Weights) :=
  (bases P br).sigma (weightSet P br)

theorem mem_indices {P : Parameters} {br : Branch} {z : Σ _ : Base,Weights} :
    z∈indices P br ↔ Core P br z.1 ∧ WeightBounds P br z.1 z.2 := by
  simp [indices,mem_bases,mem_weightSet]

def solutions (P : Parameters) (br : Branch) (b l box : ℕ) : Finset (Fin 72 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 72 => range box).filter
    fun x => (descriptor P br b l).D.Sat b (extV 72 x)

theorem mem_solutions {P : Parameters} {br : Branch} {b l box : ℕ}
    (hf : Fits P b l) (x : Fin 72 → ℕ) :
    x∈solutions P br b l box ↔ (∀i,x i<box) ∧ Relations P br (extV 72 x) := by
  simp [solutions,descriptor_sat hf]

/-- The complete descriptor counts the four
    quotient counts, once for each admissible shared arithmetic witness. -/
theorem descriptor_count {P : Parameters} {br : Branch} {b l : ℕ} (bx : ℕ → ℕ)
    (hf : Fits P b l)
    (hbox : ∀v,Core P br v → ∀w,WeightBounds P br v w →
      ∀i,canonical P br v w i<bx 0) :
    (descriptor P br b l).countB b bx =
      ∑v∈bases P br,∏k,kernelQuotient P br v k := by
  classical
  have hcard : (solutions P br b l (bx 0)).card=(indices P br).card := by
    apply card_nbij (fun x : Fin 72 → ℕ => (⟨baseOf x,weightsOf x⟩ : Σ _ : Base,Weights))
    · intro x hx
      have hr := ((mem_solutions hf x).1 hx).2
      exact mem_indices.mpr ⟨relations_core hr,relations_weights hr⟩
    · intro x hx y hy he
      have hxr := ((mem_solutions hf x).1 hx).2
      have hyr := ((mem_solutions hf y).1 hy).2
      have hb := congrArg (fun z : Σ _ : Base,Weights => z.1) he
      have hw := congrArg (fun z : Σ _ : Base,Weights => z.2) he
      change baseOf x=baseOf y at hb
      change weightsOf x=weightsOf y at hw
      rw [assignment_eq_canonical hxr,assignment_eq_canonical hyr,hb,hw]
    · rintro ⟨v,w⟩ hz
      obtain ⟨hc,hw⟩ := mem_indices.mp hz
      refine ⟨canonical P br v w,?_,?_⟩
      · exact (mem_solutions hf _).2 ⟨hbox v hc w hw,canonical_relations hc hw⟩
      · simp
  change (solutions P br b l (bx 0)).card = _
  rw [hcard,indices,card_sigma]
  exact sum_congr rfl (fun v _ => card_weightSet P br v)

open EthFollowup.Factoring EthFollowup.ExactHC

/-- The value theorem concerns the very same concrete network whose linear
    communication and fixed spread were proved in `CountKernelWF`. -/
theorem actualNetwork_value {P : Parameters} {br : Branch} {n g : ℕ} (hg : 2≤g)
    (hf : Fits P (b n) (kl n 0))
    (hbox : ∀v,Core P br v → ∀w,WeightBounds P br v w →
      ∀i,canonical P br v w i<lbox n 0) :
    ((arithSys n (actualDesc P br n) g hg).net (aLabCode n)).value =
      ((∑v∈bases P br,∏k,kernelQuotient P br v k : ℕ) : ℤ) := by
  rw [arithNet_value hg (actualDesc_WF P br n)]
  congr 1
  exact descriptor_count (lbox n) hf hbox

/-- Uniform concrete four-kernel network: exact weighted count, linear
    communication, and the counted-network node bound from input bit bounds. -/
theorem actualNetwork_bit_spec {P : Parameters} {br : Branch} {B g : ℕ}
    (hb : BitBounds P B) (hg : 2≤g) :
    let net := (arithSys (5*B+2) (actualDesc P br (5*B+2)) g hg).net (aLabCode (5*B+2))
    net.value = ((∑v∈bases P br,∏k,kernelQuotient P br v k : ℕ) : ℤ) ∧
      net.U≤2^19*132*(5*B+4) ∧ net.Is (PL (5*B+2) 132 g) 1 := by
  refine ⟨actualNetwork_value hg (bitBounds_fits hb) ?_,
    actualNetwork_communication P br hg,actualNetwork_is P br hg⟩
  intro v hc w hw
  exact canonical_lbox_bound hb hc hw

end EthFollowup.Primes.CountKernel
