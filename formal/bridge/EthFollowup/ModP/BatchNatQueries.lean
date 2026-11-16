import EthFollowup.ModP.GRate

/-! Polynomially many adaptive counting queries with a natural-number accumulator, and one fixed linear-size
network input.  The accumulator may have polynomial size; it is never used
as the network's length parameter. -/

set_option maxHeartbeats 2000000

namespace EthFollowup.ModP

open Groundwork Groundwork.Prog EthFollowup.ExactHC Eight.SecNetworks Finset Printed
  QueryMachines EthFollowup.Factoring

abbrev NatBatchIn := List Bool × ℕ × List ℕ

structure NatBatchQuerySpec where
  rounds : List Bool → ℕ
  initial : List Bool → List ℕ
  query : NatBatchIn → List Bool
  update : NatBatchIn × ℤ → List ℕ
  finish : List Bool × List ℕ → List Bool

namespace NatBatchQuery

variable {c₀ : ℕ} (pk : CntPackage c₀) (sp : NatBatchQuerySpec)

def seq (w : List Bool) : ℕ → List ℕ
  | 0 => sp.initial w
  | i+1 => sp.update ((w,i,seq w i),((pk.Q w (sp.query (w,i,seq w i)):ℕ):ℤ))

def answer (w : List Bool) : List Bool := sp.finish (w,seq pk sp w (sp.rounds w))

/-- Bounds concern the real execution sequence, not arbitrary adversarial states. -/
structure Bounds (a : ℕ) : Prop where
  rounds : ∀w, sp.rounds w ≤ a*(w.length+2)^a
  states : ∀w i, i ≤ sp.rounds w → size (seq pk sp w i) ≤ a*(w.length+2)^a
  output : ∀w, size (answer pk sp w) ≤ a*(w.length+2)^a
  valid : ∀w i, i < sp.rounds w → pk.Ok w ∧
    (sp.query (w,i,seq pk sp w i)).length ≤ pk.R w

section Machine
variable (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
  (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)

def body : Stepped NatBatchIn (List ℕ) :=
  Stepped.bind (GR.cntQ pk E kf K₀ fun p : NatBatchIn => (p.1,sp.query p))
    (Stepped.ofFun sp.update)

def loop : Stepped (List Bool) (List ℕ) :=
  Srch.iterRange sp.rounds (body pk sp E kf K₀) sp.initial

def machine : Stepped (List Bool) (List Bool) :=
  Stepped.bind (loop pk sp E kf K₀) (Stepped.ofFun sp.finish)

end Machine

variable {kf : List Unit × List Unit → Option (List Unit)} {Kf : ℕ → ℕ}
  {e : ℕ → ℝ} {C₀ : ℕ}

theorem machine_poly (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
    (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf)
    (hE : E.PolyTimeSteps) (hr : PolyT sp.rounds) (hi : PolyT sp.initial)
    (hq : PolyT sp.query) (hu : PolyT sp.update) (hf : PolyT sp.finish) :
    Nonempty (IsPolyT (machine pk sp E kf (Kf 0))) := by
  obtain ⟨i₁⟩ := GR.cntQ_poly pk E hL hk hE
    (f:=fun p : NatBatchIn => (p.1,sp.query p)) (by fun_prop)
  have : IsPolyT (Stepped.ofFun sp.update) := IsPolyT.ofFun hu
  have : IsPolyT (body pk sp E kf (Kf 0)) := IsPolyT.bind
  have : IsPolyT (loop pk sp E kf (Kf 0)) := Srch.IsPolyT.iterRange hr hi
  have : IsPolyT (Stepped.ofFun sp.finish) := IsPolyT.ofFun hf
  exact ⟨IsPolyT.bind⟩

def overhead (a qb n : ℕ) : ℕ := 10*(n+2)+5*(a*(n+2)^a)+qb*(n+2)+5

/-- One actual query followed by the actual accumulator update. -/
theorem body_runs {a : ℕ} (hb : Bounds pk sp a)
    (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
    (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)
    (w : List Bool) (i : ℕ) (hi : i < sp.rounds w) (Q : ℕ)
    (hquery : ∃t S,
      (GR.GM pk E (T2.argF kf K₀)).Runs
        (GR.ctxQ pk kf K₀ (w,sp.query (w,i,seq pk sp w i)),
          GR.ginF pk (GR.ctxQ pk kf K₀ (w,sp.query (w,i,seq pk sp w i)))
            (kN40 kf K₀ w)) t S
        ((pk.Q w (sp.query (w,i,seq pk sp w i)):ℕ):ℤ) ∧t ≤ Q ∧S ≤ Q) :
    (body pk sp E kf K₀).Runs (w,i,seq pk sp w i) (Q+2)
      (Q+overhead a pk.qb w.length) (seq pk sp w (i+1)) := by
  obtain ⟨t,S,hq,ht,hS⟩ := hquery
  have hc : (GR.cntQ pk E kf K₀ fun p : NatBatchIn => (p.1,sp.query p)).Runs
      (w,i,seq pk sp w i) t S
      ((pk.Q w (sp.query (w,i,seq pk sp w i)):ℕ):ℤ) := Stepped.mapIn_runs hq
  have hu := Stepped.ofFun_runs sp.update
    ((w,i,seq pk sp w i),((pk.Q w (sp.query (w,i,seq pk sp w i)):ℕ):ℤ))
  change (Stepped.ofFun sp.update).Runs _ _ _ (seq pk sp w (i+1)) at hu
  have hrun := Stepped.bind_runs hc hu
  apply hrun.mono (by omega)
  obtain ⟨hok,hlen⟩ := hb.valid w i hi
  have hcount := GR.size_Q_le pk hok hlen
  have hstate := hb.states w i hi.le
  have hnext := hb.states w (i+1) (by omega)
  have hiN : size i ≤ a*(w.length+2)^a+1 :=
    (Asm.size_nat_le' i).trans (by have := hb.rounds w; omega)
  change max (size (w,i,seq pk sp w i)+S)
    (max (size ((w,i,seq pk sp w i),
      ((pk.Q w (sp.query (w,i,seq pk sp w i)):ℕ):ℤ)))
      (size (seq pk sp w (i+1)))+1)+1 ≤ _
  simp only [Groundwork.size_prod,FR.size_bools] at hstate hnext ⊢
  unfold overhead
  generalize a*(w.length+2)^a = B at hstate hnext hiN ⊢
  generalize pk.qb*(w.length+2) = C at hcount ⊢
  simp only [max_def]
  split_ifs <;> omega

/-- Exact execution of the finite batch, with explicit time and state bounds. -/
theorem machine_runs_uniform {a : ℕ} (hb : Bounds pk sp a)
    (E : QueryMachine TableQuery ℤ ExplicitCost.Head ℤ)
    (kf : List Unit × List Unit → Option (List Unit)) (K₀ : ℕ)
    (w : List Bool) (Q : ℕ)
    (hbody : ∀i < sp.rounds w,
      (body pk sp E kf K₀).Runs (w,i,seq pk sp w i) (Q+2)
        (Q+overhead a pk.qb w.length) (seq pk sp w (i+1))) :
    (machine pk sp E kf K₀).Runs w
      (a*(w.length+2)^a*(Q+3)+2) (Q+2*overhead a pk.qb w.length)
      (answer pk sp w) := by
  have hl := Srch.iterRange_runs (N:=sp.rounds) (M:=body pk sp E kf K₀)
    (c₀:=sp.initial) w (seq pk sp w) rfl (fun _ => Q+2)
    (a*(w.length+2)^a) (Q+overhead a pk.qb w.length) hbody (hb.states w)
  have hf := Stepped.ofFun_runs sp.finish (w,seq pk sp w (sp.rounds w))
  change (Stepped.ofFun sp.finish).Runs _ _ _ (answer pk sp w) at hf
  have hm := Stepped.bind_runs hl hf
  apply hm.mono
  · simp only [sum_const,card_range,smul_eq_mul]
    rw [show Q+2+1=Q+3 by omega]
    have := Nat.mul_le_mul_right (Q+3) (hb.rounds w)
    omega
  · have hround : size (sp.rounds w) ≤ a*(w.length+2)^a+1 :=
      (Asm.size_nat_le' _).trans (by have := hb.rounds w; omega)
    have hstate := hb.states w (sp.rounds w) le_rfl
    have hout := hb.output w
    change max (size w+(size w+size (sp.rounds w)+
      (a*(w.length+2)^a+(Q+overhead a pk.qb w.length))+1))
      (max (size (w,seq pk sp w (sp.rounds w))) (size (answer pk sp w))+1)+1 ≤ _
    simp only [Groundwork.size_prod,FR.size_bools] at hstate hout ⊢
    unfold overhead
    generalize a*(w.length+2)^a = B at hround hstate hout ⊢
    generalize pk.qb*(w.length+2) = C at ⊢
    simp only [max_def]
    split_ifs <;> omega

open T2 in
/-- Polynomially many genuine count queries retain the original exponent.
The count network always sees w, even if the accumulator is polynomially long. -/
theorem machine_runs {a : ℕ} (hb : Bounds pk sp a)
    {C₁ : ℕ} (hC₁ : GEBody C₁) {x₀ : ℕ}
    (hL : CliqueLevels.Levels Kf e C₀) (hk : CliqueLevels.ComputesLevels Kf kf)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ)
    (hsol : CliqueLevels.Solves E Kf e C₀)
    (he : ∀l, e l ≤ ((3*x₀+6:ℕ):ℝ)/Real.sqrt (Real.logb 2 (Kf l))) :
    ∃A : ℕ, ∀w : List Bool, ∃T S : ℕ,
      (machine pk sp E kf (Kf 0)).Runs w T S (answer pk sp w) ∧
      (T:ℝ) ≤ (2:ℝ)^Xp A w.length 0 ∧ (S:ℝ) ≤ (2:ℝ)^Xp A w.length 0 ∧
      (w.length:ℝ) ≤ (2:ℝ)^Xp A w.length 0 := by
  obtain ⟨Aq,hAq⟩ := GR.query_runs pk hC₁ hL hk E hsol he
  obtain ⟨AR,hAR⟩ : ∃A, ∀n, Asm.Pol A n (overhead a pk.qb n) :=
    ⟨_,fun n => by
      unfold overhead
      exact Asm.Pol.add (Asm.Pol.add (Asm.Pol.add
        (Asm.Pol.mul (Asm.Pol.const 10) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2)))
        (Asm.Pol.mul (Asm.Pol.const 5)
          (Asm.Pol.mul (Asm.Pol.const a) (Asm.Pol.pow_n a))))
        (Asm.Pol.mul (Asm.Pol.const pk.qb) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2))))
        (Asm.Pol.const 5)⟩
  obtain ⟨AW,hAW⟩ : ∃A, ∀n, Asm.Pol A n (2*overhead a pk.qb n) :=
    ⟨_,fun n => Asm.Pol.mul (Asm.Pol.const 2) (hAR n)⟩
  let AP := 2*AW*((40*C₀+1)^2*Kf 0^40)
  let Af := AP+Aq+10
  refine ⟨Af,fun w => ?_⟩
  let n := w.length
  let Q := ⌊(2:ℝ)^Xp Aq n 0⌋₊
  have hbody : ∀i < sp.rounds w,
      (body pk sp E kf (Kf 0)).Runs (w,i,seq pk sp w i) (Q+2)
        (Q+overhead a pk.qb w.length) (seq pk sp w (i+1)) := by
    intro i hi
    obtain ⟨hok,hq⟩ := hb.valid w i hi
    obtain ⟨t,S,hr,ht,hS⟩ := hAq w (sp.query (w,i,seq pk sp w i)) hok hq
    exact body_runs pk sp hb E kf (Kf 0) w i hi Q
      ⟨t,S,hr,Nat.le_floor ht,Nat.le_floor hS⟩
  have hm := machine_runs_uniform pk sp hb E kf (Kf 0) w Q hbody
  refine ⟨_,_,hm,?_,?_,?_⟩
  all_goals
    obtain ⟨l,hKl,hK2,hup,hlo⟩ := kfacts40 kf hL hk w
    rw [←hKl] at hK2 hup hlo
    have hup30 : kN40 kf (Kf 0) w^30 ≤ Kf 0^40*(n+2) :=
      (Nat.pow_le_pow_right (by omega) (by norm_num)).trans hup
    have hW : ((2*overhead a pk.qb n:ℕ):ℝ) ≤ (2:ℝ)^Xp AP n 0 :=
      pol_le_Xp hK2 hup30 hlo (hAW n)
    have hB : ((a*(n+2)^a:ℕ):ℝ) ≤ (2:ℝ)^Xp AP n 0 := by
      apply le_trans _ hW
      exact_mod_cast (show a*(n+2)^a ≤ 2*overhead a pk.qb n by unfold overhead; omega)
    have hQ : (Q:ℝ) ≤ (2:ℝ)^Xp Aq n 0 := Nat.floor_le (by positivity)
    have hmono : ∀{A : ℕ}, A ≤ Af → (2:ℝ)^Xp A n 0 ≤ (2:ℝ)^Xp Af n 0 :=
      fun h => Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono h)
  · have hq3 := add_le_Xp hQ (const_le_Xp 3 n 0)
    have hprod := mul_le_Xp (Nat.cast_nonneg _) hB hq3
    have hsum := add_le_Xp hprod (const_le_Xp 2 n 0)
    have hfinal := hsum.trans (hmono (by unfold Af; omega))
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hfinal
  · have hsum := add_le_Xp hQ hW
    have hfinal := hsum.trans (hmono (by unfold Af; omega))
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hfinal
  · apply le_trans _ (hW.trans (hmono (by unfold Af; omega)))
    exact_mod_cast (show n ≤ 2*overhead a pk.qb n by unfold overhead; omega)

/-- One finite-alphabet Mathlib Turing machine implements the entire adaptive
batch in 2^{O(n/sqrt(log(n+2)))} time.  The number of queries, state size and
output size may all be polynomial in n; each counting network has base input w. -/
theorem machine_TM (hr : PolyT sp.rounds) (hi : PolyT sp.initial)
    (hq : PolyT sp.query) (hu : PolyT sp.update) (hf : PolyT sp.finish)
    {a : ℕ} (hb : Bounds pk sp a) :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i, Finite (M.tm.Γ i)) ∧
      ∀w : List Bool, GraphProblems.Outputs M w (answer pk sp w)
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ := by
  obtain ⟨c,x₀,C₀,D',Alg,-,-,-,-,-,he,hyp,-⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁,hC₁⟩ := T2.geBody
  exact GR.TM_of_runs _
    (machine_poly pk sp _ hyp.levels hyp.computesK hyp.steps hr hi hq hu hf) _
    (machine_runs pk sp hb hC₁ hyp.levels hyp.computesK _ hyp.solves
      (x₀:=x₀) fun l => he l)

open T2 in
theorem Xp_linear_input {A n n' L : ℕ} (hlo : n ≤ n')
    (hhi : n'+2 ≤ L*(n+2)) : Xp A n' 0 ≤ Xp (A*L) n 0 := by
  unfold Xp
  simp only [Nat.cast_zero,zero_add,Nat.cast_mul]
  rw [div_le_div_iff₀ (sq_pos _) (sq_pos _)]
  apply mul_le_mul _ (FR.sq_mono hlo) (sq_pos _).le (by positivity)
  have hh : (n':ℝ)+2 ≤ (L:ℝ)*((n:ℝ)+2) := by exact_mod_cast hhi
  calc
    (A:ℝ)*((n':ℝ)+2) ≤ (A:ℝ)*((L:ℝ)*((n:ℝ)+2)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem linear_input_TM (Mc : Stepped (List Bool) (List Bool))
    (hp : Nonempty (IsPolyT Mc)) (ans : List Bool → List Bool)
    (h : ∃A : ℕ, ∀w : List Bool, ∃T S : ℕ, Mc.Runs w T S (ans w) ∧
      (T:ℝ) ≤ (2:ℝ)^T2.Xp A w.length 0 ∧ (S:ℝ) ≤ (2:ℝ)^T2.Xp A w.length 0 ∧
      (w.length:ℝ) ≤ (2:ℝ)^T2.Xp A w.length 0)
    (pad : List Bool → List Bool) (hpad : PolyT pad)
    {L : ℕ} (hlo : ∀w, w.length ≤ (pad w).length)
    (hhi : ∀w, (pad w).length+2 ≤ L*(w.length+2)) :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i, Finite (M.tm.Γ i)) ∧
      ∀w : List Bool, GraphProblems.Outputs M w (ans (pad w))
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ := by
  obtain ⟨iM⟩ := hp
  apply GR.TM_of_runs (Stepped.mapIn pad Mc) ⟨IsPolyT.mapIn hpad⟩ (fun w => ans (pad w))
  obtain ⟨A,hA⟩ := h
  refine ⟨A*L,fun w => ?_⟩
  obtain ⟨T,S,hrun,hT,hS,hn⟩ := hA (pad w)
  have hpow : (2:ℝ)^T2.Xp A (pad w).length 0 ≤ (2:ℝ)^T2.Xp (A*L) w.length 0 :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_linear_input (hlo w) (hhi w))
  refine ⟨T,S,Stepped.mapIn_runs hrun,hT.trans hpow,hS.trans hpow,?_⟩
  exact (Nat.cast_le.mpr (hlo w)).trans (hn.trans hpow)

/-- A single polynomial-time linear-size input encoding preserves the batch
rate.  The explicit linear length premise prevents polynomial padding from
silently becoming the counting network's parameter. -/
theorem machine_TM_linear_input (hr : PolyT sp.rounds) (hi : PolyT sp.initial)
    (hq : PolyT sp.query) (hu : PolyT sp.update) (hf : PolyT sp.finish)
    {a : ℕ} (hb : Bounds pk sp a) (pad : List Bool → List Bool) (hpad : PolyT pad)
    {L : ℕ} (hlo : ∀w, w.length ≤ (pad w).length)
    (hhi : ∀w, (pad w).length+2 ≤ L*(w.length+2)) :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i, Finite (M.tm.Γ i)) ∧
      ∀w : List Bool, GraphProblems.Outputs M w (answer pk sp (pad w))
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ := by
  obtain ⟨c,x₀,C₀,D',Alg,-,-,-,-,-,he,hyp,-⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁,hC₁⟩ := T2.geBody
  exact linear_input_TM _
    (machine_poly pk sp _ hyp.levels hyp.computesK hyp.steps hr hi hq hu hf) _
    (machine_runs pk sp hb hC₁ hyp.levels hyp.computesK _ hyp.solves
      (x₀:=x₀) fun l => he l) pad hpad hlo hhi

end NatBatchQuery
end EthFollowup.ModP
