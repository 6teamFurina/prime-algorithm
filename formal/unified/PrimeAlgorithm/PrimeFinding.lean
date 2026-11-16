import PrimeAlgorithm.PrimeSumMachine
import Mathlib.NumberTheory.Bertrand

/- ! Deterministic binary search using exact prefix sums of primes.  -/
set_option maxHeartbeats 800000
noncomputable section
namespace PrimeAlgorithm.PrimeFinding
open Groundwork EthFollowup.ModP EthFollowup.Factoring

 theorem primeSum_mono : Monotone primeSum := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

theorem primeSum_lt_add_iff (a d : ℕ) :
    primeSum a  <  primeSum (a + d) ↔ ∃p, a < p  ∧  p ≤ a + d  ∧  p.Prime := by
  induction d with
  | zero => simp only [Nat.add_zero,lt_self_iff_false,false_iff,not_exists]; intro p; omega
  | succ d ih => 
    rw [Nat.add_succ,primeSum_succ]
    have hm := primeSum_mono (show a ≤ a + d by omega)
    by_cases hp : (a + d + 1).Prime
    · simp only [if_pos hp]
      constructor
      · intro _; exact ⟨a + d + 1,by omega,by omega,hp⟩
      · intro _; omega
    · simp only [if_neg hp,Nat.add_zero]
      rw [ih]
      constructor
      · rintro ⟨p,ha,hb,hpr⟩; exact ⟨p,ha,by omega,hpr⟩
      · rintro ⟨p,ha,hb,hpr⟩
        refine ⟨p,ha,?_,hpr⟩
        have : p≠a + d + 1 := by intro he; subst p; contradiction
        omega

theorem primeSum_lt_iff {a b : ℕ} (hab : a ≤ b) :
    primeSum a  <  primeSum b ↔ ∃p, a < p  ∧  p ≤ b  ∧  p.Prime := by
  simpa [Nat.add_sub_of_le hab] using primeSum_lt_add_iff a (b - a)

abbrev State := ℕ × ℕ × ℕ

def middle (s : State) : ℕ := (s.1 + s.2.1)/2

def bisect (s : State) : State :=
  if s.2.2  <  primeSum (middle s) then (s.1,middle s,s.2.2)
  else (middle s,s.2.1,s.2.2)

def initial (N : ℕ) : State := (N,2 * max N 1,primeSum N)

def search (N k : ℕ) : State := bisect^[k] (initial N)

def Invariant (N : ℕ) (s : State) : Prop :=
  N ≤ s.1  ∧  s.1 < s.2.1  ∧  s.2.1 ≤ 2 * max N 1  ∧ 
  s.2.2=primeSum N  ∧  primeSum s.1=primeSum N  ∧  primeSum N < primeSum s.2.1

theorem initial_invariant (N : ℕ) : Invariant N (initial N) := by
  have hM : max N 1≠0 := by omega
  obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul (max N 1) hM
  have hN : N < p := by omega
  have hs := (primeSum_lt_iff (show N ≤ 2 * max N 1 by omega)).2 ⟨p,hN,hu,hp⟩
  change N ≤ N ∧ N < 2 * max N 1 ∧ _
  exact ⟨le_rfl,by omega,le_rfl,rfl,rfl,hs⟩

theorem bisect_invariant {N : ℕ} {s : State} (h : Invariant N s) :
    Invariant N (bisect s) := by
  rcases s with ⟨lo,hi,base⟩
  dsimp [Invariant] at h
  rcases h with ⟨hN,hlo,hhi,hbase,hslo,hshi⟩
  have hmlo : lo ≤ (lo + hi)/2 := by omega
  have hmhi : (lo + hi)/2 < hi := by omega
  have hs := primeSum_mono hmlo
  unfold Invariant bisect middle
  dsimp only
  split_ifs with h
  all_goals dsimp only
  · have hm : lo ≠ (lo + hi)/2 := by
      intro he
      rw [←he,hslo,←hbase] at h
      omega
    exact ⟨hN,by omega,by omega,hbase,hslo,by simpa [hbase] using h⟩
  · refine ⟨by omega,hmhi,hhi,hbase,?_,hshi⟩
    simp only [hbase] at h
    omega

theorem bisect_width {s : State} {k : ℕ} (hlo : s.1 < s.2.1)
    (hw : s.2.1 - s.1 ≤ 2^(k + 1)) :
    (bisect s).2.1 - (bisect s).1 ≤ 2^k := by
  rcases s with ⟨lo,hi,base⟩
  dsimp only at hlo hw
  unfold bisect middle
  dsimp only
  rw [pow_succ] at hw
  split_ifs <;> simp only [Prod.fst,Prod.snd] <;> omega

theorem search_invariant (N k : ℕ) : Invariant N (search N k) := by
  induction k with
  | zero =>  exact initial_invariant N
  | succ k ih => 
    simpa [search,Function.iterate_succ_apply'] using bisect_invariant ih

theorem search_width (N k r : ℕ) (h : (initial N).2.1 - (initial N).1 ≤ 2^(r + k)) :
    (search N k).2.1 - (search N k).1 ≤ 2^r := by
  induction k generalizing r with
  | zero =>  simpa [search] using h
  | succ k ih => 
    have hh := ih (r + 1) (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h)
    simpa [search,Function.iterate_succ_apply'] using bisect_width (search_invariant N k).2.1 hh

theorem search_prime (N k : ℕ) (hw : (initial N).2.1 - (initial N).1 ≤ 2^k) :
    (search N k).2.1.Prime  ∧  N < (search N k).2.1  ∧  (search N k).2.1 ≤ 2 * max N 1 := by
  have hi := search_invariant N k
  have hlo := hi.2.1
  have hN := hi.1
  have hh := search_width N k 0 (by simpa using hw)
  have he : (search N k).2.1=(search N k).1 + 1 := by simp only [pow_zero] at hh; omega
  have hs : primeSum (search N k).1  <  primeSum ((search N k).1 + 1) := by
    rw [←he,hi.2.2.2.2.1]; exact hi.2.2.2.2.2
  rw [primeSum_succ] at hs
  have hp : ((search N k).1 + 1).Prime := by
    by_contra h; simp [h] at hs
  exact ⟨by rwa [he],by omega,hi.2.2.1⟩

end PrimeAlgorithm.PrimeFinding
