import EthFollowup.ModP.BatchNatQueries

/-! Adaptive polynomially many calls to a subexponential word machine.
All running-time and space bounds refer to the original input length. -/
set_option maxHeartbeats 2000000
namespace PrimeAlgorithm
open Groundwork Groundwork.Prog EthFollowup.ModP EthFollowup.ExactHC
  Eight.SecNetworks Finset Printed QueryMachines EthFollowup.Factoring

structure WordQuerySpec (γ : Type) where
  rounds : List Bool → ℕ
  initial : List Bool → γ
  query : (List Bool × ℕ × γ) → List Bool
  update : (List Bool × ℕ × γ) × List Bool → γ
  finish : List Bool × γ → List Bool

namespace AdaptiveWordQuery
variable {γ : Type} [Enc γ] [HasSize γ] [Carried γ]
variable (ans : List Bool → List Bool) (sp : WordQuerySpec γ)

def seq (w : List Bool) : ℕ → γ
  | 0 => sp.initial w
  | i+1 => sp.update ((w,i,seq w i),ans (sp.query (w,i,seq w i)))
def answer (w : List Bool) : List Bool := sp.finish (w,seq ans sp w (sp.rounds w))

structure Bounds (a L : ℕ) : Prop where
  rounds : ∀w, sp.rounds w ≤ a*(w.length+2)^a
  states : ∀w i, i ≤ sp.rounds w → size (seq ans sp w i) ≤ a*(w.length+2)^a
  output : ∀w, size (answer ans sp w) ≤ a*(w.length+2)^a
  values : ∀w i, i < sp.rounds w → size (ans (sp.query (w,i,seq ans sp w i))) ≤ a*(w.length+2)^a
  lower : ∀w i, i < sp.rounds w → w.length ≤ (sp.query (w,i,seq ans sp w i)).length
  upper : ∀w i, i < sp.rounds w → (sp.query (w,i,seq ans sp w i)).length+2 ≤ L*(w.length+2)

variable (Mc : Stepped (List Bool) (List Bool))
def body : Stepped (List Bool × ℕ × γ) γ :=
  Stepped.bind (Stepped.mapIn sp.query Mc) (Stepped.ofFun sp.update)
def loop : Stepped (List Bool) γ := Srch.iterRange sp.rounds (body sp Mc) sp.initial
def machine : Stepped (List Bool) (List Bool) :=
  Stepped.bind (loop sp Mc) (Stepped.ofFun sp.finish)

theorem machine_poly (hp : Nonempty (IsPolyT Mc))
    (hr : PolyT sp.rounds) (hi : PolyT sp.initial) (hq : PolyT sp.query)
    (hu : PolyT sp.update) (hf : PolyT sp.finish) : Nonempty (IsPolyT (machine sp Mc)) := by
  obtain ⟨iM⟩ := hp
  have : IsPolyT (Stepped.mapIn sp.query Mc) := IsPolyT.mapIn hq
  have : IsPolyT (Stepped.ofFun sp.update) := IsPolyT.ofFun hu
  have : IsPolyT (body sp Mc) := IsPolyT.bind
  have : IsPolyT (loop sp Mc) := Srch.IsPolyT.iterRange hr hi
  have : IsPolyT (Stepped.ofFun sp.finish) := IsPolyT.ofFun hf
  exact ⟨IsPolyT.bind⟩

def overhead (a n : ℕ) : ℕ := 10*(n+2)+10*(a*(n+2)^a)+10

theorem body_runs {a L : ℕ} (hb : Bounds ans sp a L)
    (w : List Bool) (i : ℕ) (hi : i < sp.rounds w) (Q : ℕ)
    (hquery : ∃t S, Mc.Runs (sp.query (w,i,seq ans sp w i)) t S
      (ans (sp.query (w,i,seq ans sp w i))) ∧ t≤Q ∧ S≤Q) :
    (body sp Mc).Runs (w,i,seq ans sp w i) (Q+2)
      (Q+overhead a w.length) (seq ans sp w (i+1)) := by
  obtain ⟨t,S,hq,ht,hS⟩ := hquery
  have hc : (Stepped.mapIn sp.query Mc).Runs (w,i,seq ans sp w i) t S
      (ans (sp.query (w,i,seq ans sp w i))) := Stepped.mapIn_runs hq
  have hu := Stepped.ofFun_runs sp.update
    ((w,i,seq ans sp w i),ans (sp.query (w,i,seq ans sp w i)))
  change (Stepped.ofFun sp.update).Runs _ _ _ (seq ans sp w (i+1)) at hu
  have hrun := Stepped.bind_runs hc hu
  apply hrun.mono (by omega)
  have hval := hb.values w i hi
  have hstate := hb.states w i hi.le
  have hnext := hb.states w (i+1) (by omega)
  have hiN : size i ≤ a*(w.length+2)^a+1 :=
    (Asm.size_nat_le' i).trans (by have := hb.rounds w; omega)
  change max (size (w,i,seq ans sp w i)+S)
    (max (size ((w,i,seq ans sp w i),ans (sp.query (w,i,seq ans sp w i))))
      (size (seq ans sp w (i+1)))+1)+1 ≤ _
  simp only [Groundwork.size_prod,FR.size_bools] at hstate hnext hval ⊢
  unfold overhead
  generalize a*(w.length+2)^a = B at hstate hnext hiN hval ⊢
  simp only [max_def]
  split_ifs <;> omega

theorem machine_runs_uniform {a L : ℕ} (hb : Bounds ans sp a L)
    (w : List Bool) (Q : ℕ)
    (hbody : ∀i < sp.rounds w,
      (body sp Mc).Runs (w,i,seq ans sp w i) (Q+2)
        (Q+overhead a w.length) (seq ans sp w (i+1))) :
    (machine sp Mc).Runs w
      (a*(w.length+2)^a*(Q+3)+2) (Q+2*overhead a w.length)
      (answer ans sp w) := by
  have hl := Srch.iterRange_runs (N:=sp.rounds) (M:=body sp Mc)
    (c₀:=sp.initial) w (seq ans sp w) rfl (fun _ => Q+2)
    (a*(w.length+2)^a) (Q+overhead a w.length) hbody (hb.states w)
  have hf := Stepped.ofFun_runs sp.finish (w,seq ans sp w (sp.rounds w))
  change (Stepped.ofFun sp.finish).Runs _ _ _ (answer ans sp w) at hf
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
      (a*(w.length+2)^a+(Q+overhead a w.length))+1))
      (max (size (w,seq ans sp w (sp.rounds w))) (size (answer ans sp w))+1)+1 ≤ _
    simp only [Groundwork.size_prod,FR.size_bools] at hstate hout ⊢
    unfold overhead
    generalize a*(w.length+2)^a = B at hround hstate hout ⊢
    simp only [max_def]
    split_ifs <;> omega

open T2 in
theorem overhead_bound (a : ℕ) : ∃A, ∀n,
    ((2*overhead a n:ℕ):ℝ) ≤ (2:ℝ)^Xp A n 0 := by
  obtain ⟨c,x₀,C₀,D',Alg,-,-,-,-,-,he,hyp,-⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨AW,hAW⟩ : ∃A, ∀n, Asm.Pol A n (2*overhead a n) :=
    ⟨_,fun n => by
      unfold overhead
      exact Asm.Pol.mul (Asm.Pol.const 2) (Asm.Pol.add (Asm.Pol.add
        (Asm.Pol.mul (Asm.Pol.const 10) (Asm.Pol.add Asm.Pol.id (Asm.Pol.const 2)))
        (Asm.Pol.mul (Asm.Pol.const 10) (Asm.Pol.mul (Asm.Pol.const a) (Asm.Pol.pow_n a))))
        (Asm.Pol.const 10))⟩
  refine ⟨2*AW*((40*C₀+1)^2*(Levels.Gen.K x₀) 0^40),fun n=>?_⟩
  obtain ⟨l,hKl,hK2,hup,hlo⟩ := kfacts40 (CliqueLevels.levelsUnder x₀) hyp.levels hyp.computesK (List.replicate n false)
  rw [←hKl] at hK2 hup hlo
  simp only [List.length_replicate] at hup hlo
  have hup30 : kN40 (CliqueLevels.levelsUnder x₀) ((Levels.Gen.K x₀) 0) (List.replicate n false)^30 ≤ (Levels.Gen.K x₀) 0^40*(n+2) :=
    (Nat.pow_le_pow_right (by omega) (by norm_num)).trans hup
  exact pol_le_Xp hK2 hup30 hlo (hAW n)

open T2 in
theorem machine_runs {a L : ℕ} (hb : Bounds ans sp a L)
    (h : ∃A : ℕ, ∀w : List Bool, ∃T S : ℕ, Mc.Runs w T S (ans w) ∧
      (T:ℝ) ≤ (2:ℝ)^Xp A w.length 0 ∧ (S:ℝ) ≤ (2:ℝ)^Xp A w.length 0 ∧
      (w.length:ℝ) ≤ (2:ℝ)^Xp A w.length 0) :
    ∃A : ℕ, ∀w : List Bool, ∃T S : ℕ, (machine sp Mc).Runs w T S (answer ans sp w) ∧
      (T:ℝ) ≤ (2:ℝ)^Xp A w.length 0 ∧ (S:ℝ) ≤ (2:ℝ)^Xp A w.length 0 ∧
      (w.length:ℝ) ≤ (2:ℝ)^Xp A w.length 0 := by
  obtain ⟨Ao,hAo⟩ := h
  obtain ⟨AP,hAP⟩ := overhead_bound a
  let Aq := Ao*L
  let Af := AP+Aq+10
  refine ⟨Af,fun w=>?_⟩
  let n := w.length
  let Q := ⌊(2:ℝ)^Xp Aq n 0⌋₊
  have hbody : ∀i < sp.rounds w,
      (body sp Mc).Runs (w,i,seq ans sp w i) (Q+2)
        (Q+overhead a w.length) (seq ans sp w (i+1)) := by
    intro i hi
    obtain ⟨t,S,hr,ht,hS,-⟩ := hAo (sp.query (w,i,seq ans sp w i))
    have hp : (2:ℝ)^Xp Ao (sp.query (w,i,seq ans sp w i)).length 0 ≤ (2:ℝ)^Xp Aq n 0 :=
      Real.rpow_le_rpow_of_exponent_le one_le_two
        (NatBatchQuery.Xp_linear_input (hb.lower w i hi) (hb.upper w i hi))
    exact body_runs ans sp Mc hb w i hi Q ⟨t,S,hr,Nat.le_floor (ht.trans hp),Nat.le_floor (hS.trans hp)⟩
  refine ⟨_,_,machine_runs_uniform ans sp Mc hb w Q hbody,?_,?_,?_⟩
  all_goals
    have hW := hAP n
    have hB : ((a*(n+2)^a:ℕ):ℝ) ≤ (2:ℝ)^Xp AP n 0 := by
      apply le_trans _ hW
      exact_mod_cast (show a*(n+2)^a ≤ 2*overhead a n by unfold overhead; omega)
    have hQ : (Q:ℝ) ≤ (2:ℝ)^Xp Aq n 0 := Nat.floor_le (by positivity)
    have hmono : ∀{A : ℕ}, A ≤ Af → (2:ℝ)^Xp A n 0 ≤ (2:ℝ)^Xp Af n 0 :=
      fun h=>Real.rpow_le_rpow_of_exponent_le one_le_two (Xp_mono h)
  · have hh := add_le_Xp (mul_le_Xp (Nat.cast_nonneg _) hB (add_le_Xp hQ (const_le_Xp 3 n 0))) (const_le_Xp 2 n 0)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh.trans (hmono (by unfold Af; omega))
  · have hh := add_le_Xp hQ hW
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh.trans (hmono (by unfold Af; omega))
  · apply le_trans _ (hW.trans (hmono (by unfold Af; omega)))
    exact_mod_cast (show n ≤ 2*overhead a n by unfold overhead; omega)

theorem machine_TM (hp : Nonempty (IsPolyT Mc))
    (hr : PolyT sp.rounds) (hi : PolyT sp.initial) (hq : PolyT sp.query)
    (hu : PolyT sp.update) (hf : PolyT sp.finish) {a L : ℕ} (hb : Bounds ans sp a L)
    (h : ∃A : ℕ, ∀w : List Bool, ∃T S : ℕ, Mc.Runs w T S (ans w) ∧
      (T:ℝ) ≤ (2:ℝ)^T2.Xp A w.length 0 ∧ (S:ℝ) ≤ (2:ℝ)^T2.Xp A w.length 0 ∧
      (w.length:ℝ) ≤ (2:ℝ)^T2.Xp A w.length 0) :
    ∃(M : Turing.TM2ComputableAux Bool Bool) (C : ℕ), (∀i,Finite (M.tm.Γ i)) ∧
      ∀w : List Bool, GraphProblems.Outputs M w (answer ans sp w)
        ⌊(C:ℝ)*2^((C:ℝ)*w.length/Real.sqrt (Real.logb 2 (w.length+2)))⌋₊ :=
  GR.TM_of_runs _ (machine_poly sp Mc hp hr hi hq hu hf) _ (machine_runs ans sp Mc hb h)
end AdaptiveWordQuery
end PrimeAlgorithm
