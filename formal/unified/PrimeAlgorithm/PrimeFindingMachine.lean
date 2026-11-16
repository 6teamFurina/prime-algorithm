import PrimeAlgorithm.UnifiedSpecification
import PrimeAlgorithm.PrimeFinding
import PrimeAlgorithm.AdaptiveWordQueries
import PrimeAlgorithm.PrimeSumOracle

set_option maxHeartbeats 1000000
noncomputable section
namespace PrimeAlgorithm.PrimeFinding
open Groundwork Groundwork.Prog EthFollowup.ModP EthFollowup.Factoring EthFollowup.ExactHC

abbrev Input := List Bool × ℕ × State

def request (p : Input) : ℕ := if p.2.1 = 0 then ofWord p.1 else middle p.2.2

def query (p : Input) : List Bool :=
  Nat.bits (request p) ++ (p.1 ++ [false,false]).map (fun _ => false)

def update (p : Input × List Bool) : State :=
  if p.1.2.1 = 0 then (p.1.2.2.1,p.1.2.2.2.1,ofWord p.2)
  else if p.1.2.2.2.2 < ofWord p.2 then
    (p.1.2.2.1,middle p.1.2.2,p.1.2.2.2.2)
  else (middle p.1.2.2,p.1.2.2.2.1,p.1.2.2.2.2)

def spec : WordQuerySpec State where
  rounds w := w.length+3
  initial w := (ofWord w,2*max (ofWord w) 1,0)
  query := query
  update := update
  finish p := Nat.bits p.2.2.1

def sumAnswer (w : List Bool) : List Bool := Nat.bits (primeSum (ofWord w))

theorem query_value (p : Input) : ofWord (query p) = request p := by
  rw [query,List.map_const',gofWord_append_replicate_false,FR.ofWord_bits]

theorem query_length (p : Input) :
    (query p).length = (Nat.bits (request p)).length+p.1.length+2 := by
  simp [query,Nat.add_assoc]

theorem rounds_polyT : PolyT spec.rounds := by unfold spec; fun_prop
theorem initial_polyT : PolyT spec.initial := by unfold spec; fun_prop
theorem query_polyT : PolyT spec.query := by unfold spec query request middle; fun_prop
theorem update_polyT : PolyT spec.update := by unfold spec update middle; fun_prop
theorem finish_polyT : PolyT spec.finish := by unfold spec; fun_prop

theorem seq_succ (w : List Bool) (k : ℕ) :
    AdaptiveWordQuery.seq sumAnswer spec w (k+1) = search (ofWord w) k := by
  induction k with
  | zero =>
    simp [AdaptiveWordQuery.seq,spec,update,sumAnswer,query_value,request,search,initial,FR.ofWord_bits]
  | succ k ih =>
    rw [AdaptiveWordQuery.seq,ih]
    simp only [spec,update,sumAnswer,query_value,request,Nat.add_eq_zero_iff,
      Nat.one_ne_zero,and_false,if_false,FR.ofWord_bits]
    change bisect (search (ofWord w) k) = search (ofWord w) (k+1)
    simp only [search,Function.iterate_succ_apply']

def found (w : List Bool) : ℕ := (search (ofWord w) (w.length+2)).2.1

theorem answer_eq (w : List Bool) :
    AdaptiveWordQuery.answer sumAnswer spec w = Nat.bits (found w) := by
  dsimp only [AdaptiveWordQuery.answer]
  change spec.finish (w,AdaptiveWordQuery.seq sumAnswer spec w (w.length+3)) = _
  rw [show w.length+3 = (w.length+2)+1 by omega,seq_succ]
  rfl

theorem upper_lt (w : List Bool) : 2*max (ofWord w) 1 < 2^(w.length+2) := by
  have h := Groundwork.ofWord_lt w
  have hp : 0 < 2^w.length := by positivity
  rw [pow_add]
  norm_num
  omega

theorem found_spec (w : List Bool) :
    (found w).Prime ∧ ofWord w < found w ∧ found w ≤ 2*max (ofWord w) 1 := by
  apply search_prime
  have h := upper_lt w
  dsimp [initial]
  omega

theorem request_lt (w : List Bool) (i : ℕ) :
    request (w,i,AdaptiveWordQuery.seq sumAnswer spec w i) < 2^(w.length+2) := by
  cases i with
  | zero =>
    simp only [request,if_pos rfl]
    have h := Groundwork.ofWord_lt w
    exact h.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  | succ i =>
    rw [seq_succ]
    have h := search_invariant (ofWord w) i
    have h1 := h.2.1
    have h2 := h.2.2.1
    have h3 := upper_lt w
    simp only [request,Nat.succ_ne_zero,if_false,middle]
    omega

theorem query_bounds (w : List Bool) (i : ℕ) :
    w.length ≤ (query (w,i,AdaptiveWordQuery.seq sumAnswer spec w i)).length ∧
    (query (w,i,AdaptiveWordQuery.seq sumAnswer spec w i)).length+2 ≤ 3*(w.length+2) := by
  rw [query_length]
  have h := bits_length_le (request_lt w i)
  dsimp only
  omega

theorem state_size (w : List Bool) (i : ℕ) :
    size (AdaptiveWordQuery.seq sumAnswer spec w i) ≤ 4*w.length+7 := by
  have hN := Groundwork.ofWord_lt w
  have hsN := Asm.size_nat_of_lt hN
  have hsum := Asm.size_nat_of_lt (primeSum_lt_two_pow hN)
  cases i with
  | zero =>
    have hhi := Asm.size_nat_of_lt (upper_lt w)
    change size (ofWord w) + (size (2*max (ofWord w) 1) + size (0:ℕ)) ≤ _
    norm_num [Groundwork.size_nat] at *
    omega
  | succ i =>
    rw [seq_succ]
    have h := search_invariant (ofWord w) i
    have h1 := h.2.1
    have h2 := h.2.2.1
    have h3 := upper_lt w
    have hlo : (search (ofWord w) i).1 < 2^(w.length+2) := by omega
    have hhi : (search (ofWord w) i).2.1 < 2^(w.length+2) := by omega
    have hslos := Asm.size_nat_of_lt hlo
    have hshis := Asm.size_nat_of_lt hhi
    simp only [Groundwork.size_prod,h.2.2.2.1]
    omega

theorem output_size (w : List Bool) :
    size (AdaptiveWordQuery.answer sumAnswer spec w) ≤ 2*w.length+5 := by
  rw [answer_eq,FR.size_bools]
  have h := (found_spec w).2.2
  have hh := upper_lt w
  have hl := bits_length_le (show found w < 2^(w.length+2) by omega)
  omega

theorem value_size (w : List Bool) (i : ℕ) :
    size (sumAnswer (query (w,i,AdaptiveWordQuery.seq sumAnswer spec w i))) ≤ 4*w.length+9 := by
  rw [sumAnswer,query_value,FR.size_bools]
  have hl := bits_length_le (primeSum_lt_two_pow (request_lt w i))
  omega

theorem bounds : AdaptiveWordQuery.Bounds sumAnswer spec 10 3 := by
  have poly (n : ℕ) : 4*n+9 ≤ 10*(n+2)^10 := by
    have hp : n+2 ≤ (n+2)^10 := Nat.le_pow (by omega)
    omega
  constructor
  · intro w; change w.length+3 ≤ _; have := poly w.length; omega
  · intro w i _; exact (state_size w i).trans (by have := poly w.length; omega)
  · intro w; exact (output_size w).trans (by have := poly w.length; omega)
  · intro w i _; exact (value_size w i).trans (poly w.length)
  · intro w i _; exact (query_bounds w i).1
  · intro w i _; exact (query_bounds w i).2

end PrimeAlgorithm.PrimeFinding

namespace PrimeAlgorithm.PrimeFindingMachine
open Groundwork PrimeFinding

/-- The complete search uses one initial prefix sum and `b+2` midpoint sums. -/
theorem oracle_calls (w : List Bool) : spec.rounds w = w.length+3 := rfl

def findPrime (N : ℕ) : ℕ := found (Nat.bits N)

theorem findPrime_spec (N : ℕ) :
    (findPrime N).Prime ∧ N < findPrime N ∧ findPrime N ≤ 2*max N 1 := by
  simpa only [findPrime,EthFollowup.Factoring.FR.ofWord_bits] using found_spec (Nat.bits N)

theorem findPrime_positive {N : ℕ} (hN : 1 ≤ N) :
    (findPrime N).Prime ∧ N < findPrime N ∧ findPrime N ≤ 2*N := by
  simpa only [max_eq_left hN] using findPrime_spec N

/-- One deterministic finite-alphabet machine implements all adaptive sum calls,
state updates and final binary output within the original subexponential rate. -/
theorem primeFinding_TM :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i,Finite (M.tm.Γ i)) ∧
      ∀w : List Bool, GraphProblems.Outputs M w (Nat.bits (found w))
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ := by
  obtain ⟨Mc,hpoly,hruns⟩ := PrimeSumOracle.primeSum_stepped
  obtain ⟨M,C,hfinite,hM⟩ := AdaptiveWordQuery.machine_TM sumAnswer spec Mc hpoly
    rounds_polyT initial_polyT query_polyT update_polyT finish_polyT bounds hruns
  refine ⟨M,C,hfinite,fun w => ?_⟩
  simpa only [answer_eq] using hM w

/-- Every natural input is covered, including zero (which returns the prime 2).
For positive `N`, the output lies in `(N,2N]`. The same machine and constant work
for all inputs, and the bound uses the original input's binary length. -/
theorem primeFinding_TM_all_inputs :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i,Finite (M.tm.Γ i)) ∧
      ∀N : ℕ, (findPrime N).Prime ∧ N < findPrime N ∧ findPrime N ≤ 2*max N 1 ∧
        GraphProblems.Outputs M (Nat.bits N) (Nat.bits (findPrime N))
          ⌊(C:ℝ)*2^((C:ℝ)*(Nat.bits N).length/
            Real.sqrt (Real.logb 2 ((Nat.bits N).length+2)))⌋₊ := by
  obtain ⟨M,C,hfinite,hM⟩ := primeFinding_TM
  refine ⟨M,C,hfinite,fun N => ?_⟩
  obtain ⟨hp,hl,hu⟩ := findPrime_spec N
  exact ⟨hp,hl,hu,hM (Nat.bits N)⟩

end PrimeAlgorithm.PrimeFindingMachine
