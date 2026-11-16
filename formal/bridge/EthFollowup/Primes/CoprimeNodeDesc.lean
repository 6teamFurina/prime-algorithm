/-
A real ArithL node for coprime multiplication. Variables are A, B, P, u, v.
P = A*B and A*u = 1+B*v, with u<B, v<A and A,B>=2.

Products belong to one chain each. The proof is independent of the 4.35 main
project: the bounded Bezout argument is reproduced for this 4.33.1 bridge.
The pinned description counts exactly one assignment for coprime A,B.
-/
import EthFollowup.Primes.ArithLDesc
import EthFollowup.ModP.ArithInstances
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.CoprimeNode

open Finset EthFollowup.ModP

def Certificate (a b u v : ℕ) : Prop := u < b ∧ v < a ∧ a * u = 1 + b * v

instance (a b u v : ℕ) : Decidable (Certificate a b u v) := by
  unfold Certificate; infer_instance

theorem Certificate.coprime {a b u v : ℕ} (h : Certificate a b u v) : a.Coprime b := by
  have hleft : a.gcd b ∣ a * u := dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) u
  have hright : a.gcd b ∣ b * v := dvd_mul_of_dvd_left (Nat.gcd_dvd_right a b) v
  rw [h.2.2] at hleft
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_left hright).2 hleft)

theorem certificate_exists {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : a.Coprime b) :
    ∃ u v, Certificate a b u v := by
  obtain ⟨u, hu, hmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hb
  have heq : a * u = 1 + b * (a * u / b) := by
    have h := Nat.mod_add_div (a * u) b
    rw [hmod] at h
    omega
  refine ⟨u, a * u / b, hu, ?_, heq⟩
  have hmul : a * u < a * b := Nat.mul_lt_mul_of_pos_left hu (by omega)
  nlinarith

theorem Certificate.unique {a b u v u' v' : ℕ} (hb : 0 < b)
    (h : Certificate a b u v) (h' : Certificate a b u' v') : u = u' ∧ v = v' := by
  have hm : Nat.ModEq b (a * u) (a * u') := by
    change (a * u) % b = (a * u') % b
    rw [h.2.2, h'.2.2]
    simp
  have hm' := Nat.ModEq.cancel_left_of_coprime h.coprime.symm hm
  have hu : u = u' := by
    change u % b = u' % b at hm'
    simpa [Nat.mod_eq_of_lt h.1, Nat.mod_eq_of_lt h'.1] using hm'
  refine ⟨hu, ?_⟩
  have he := h.2.2
  have he' := h'.2.2
  nlinarith

/-- No intermediate product in the certificate exceeds the parent product. -/
theorem Certificate.product_bounds {a b u v : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : Certificate a b u v) : a * u < a * b ∧ b * v < a * b := by
  refine ⟨Nat.mul_lt_mul_of_pos_left h.1 ha, ?_⟩
  have := Nat.mul_lt_mul_of_pos_left h.2.1 hb
  nlinarith

def products : List ProdD :=
  [⟨0, .var 1⟩, ⟨2, .const [1]⟩, ⟨0, .var 3⟩, ⟨1, .var 4⟩]

def chains : List ChainD :=
  [⟨[⟨1, .prod 1⟩], [⟨1, .prod 0⟩]⟩,
   ⟨[⟨1, .prod 2⟩], [⟨1, .const [1]⟩, ⟨1, .prod 3⟩]⟩]

def mkDesc (cs : List CmpD) : LDesc where
  D := { nV := 5, pat := [], prods := products, chains := chains, cmps := cs }
  lev := []
  levC := []

def comparisons (b l0 : ℕ) : List CmpD :=
  [⟨0, .const (toLimbs b l0 2), .ge⟩, ⟨1, .const (toLimbs b l0 2), .ge⟩,
   ⟨3, .var 1, .lt⟩, ⟨4, .var 0, .lt⟩]

/-- Reusable node: A and B are free input variables. -/
def nodeDesc (b l0 : ℕ) : LDesc := mkDesc (comparisons b l0)

/-- The same node with its two inputs fixed, for the exact one-solution theorem. -/
def pinnedDesc (b l0 a c : ℕ) : LDesc :=
  mkDesc (comparisons b l0 ++
    [⟨0, .const (toLimbs b l0 a), .eq⟩, ⟨1, .const (toLimbs b l0 c), .eq⟩])

@[simp] theorem mkDesc_lv (cs : List CmpD) (v : ℕ) : (mkDesc cs).lv v = 0 := rfl
@[simp] theorem mkDesc_lc (cs : List CmpD) (j : ℕ) : (mkDesc cs).lc j = 0 := rfl
@[simp] theorem mkDesc_lp (cs : List CmpD) (j : ℕ) : (mkDesc cs).lp j = 0 := rfl
@[simp] theorem mkDesc_lq (cs : List CmpD) (j : ℕ) : (mkDesc cs).lq j = 0 := rfl

theorem nodeDesc_sat {b l0 : ℕ} (h2 : 2 < 2 ^ (b * l0)) (x : ℕ → ℕ) :
    (nodeDesc b l0).D.Sat b x ↔
      2 ≤ x 0 ∧ 2 ≤ x 1 ∧ x 2 = x 0 * x 1 ∧ Certificate (x 0) (x 1) (x 3) (x 4) := by
  simp [nodeDesc, mkDesc, comparisons, Desc.Sat, patMatch, CmpRel.Holds,
    Operand.eval, limbsVal_toLimbs h2, products, chains, sideVal, Src.eval, ProdD.eval,
    Certificate, show limbsVal b [1] = 1 by simp [limbsVal]]
  tauto

theorem pinnedDesc_sat {b l0 a c : ℕ} (h2 : 2 < 2 ^ (b * l0))
    (ha : a < 2 ^ (b * l0)) (hc : c < 2 ^ (b * l0)) (x : ℕ → ℕ) :
    (pinnedDesc b l0 a c).D.Sat b x ↔
      x 0 = a ∧ x 1 = c ∧ 2 ≤ a ∧ 2 ≤ c ∧ x 2 = a * c ∧ Certificate a c (x 3) (x 4) := by
  simp [pinnedDesc, mkDesc, comparisons, Desc.Sat, patMatch, CmpRel.Holds,
    Operand.eval, limbsVal_toLimbs h2, limbsVal_toLimbs ha, limbsVal_toLimbs hc,
    products, chains, sideVal, Src.eval, ProdD.eval, Certificate,
    show limbsVal b [1] = 1 by simp [limbsVal]]
  aesop

/-- This generic node accepts any additional legal comparisons. -/
theorem mkDesc_WFB {b l0 : ℕ} (cs : List CmpD) (lk : ℕ → ℕ)
    (hb : 1 ≤ b) (hl : 1 ≤ l0) (hl0 : lk 0 = l0)
    (hcs : ∀ q ∈ cs, q.v < 5 ∧ q.rhs.OK b l0 5) : (mkDesc cs).WFB b lk where
  pat_len := by intro v hv; simp [mkDesc]
  prod_ok := by
    intro p hp
    have hp' : p < 4 := by simpa [mkDesc, products] using hp
    have hc : (mkDesc cs).D.chainOf p < 2 := by
      change (chains.findIdx fun ch => decide (ch.HasProd p)) < 2
      interval_cases p <;> decide
    have h1 : 1 < 2 ^ b := Nat.one_lt_two_pow (by omega)
    interval_cases p <;>
      simp [mkDesc, products, chains, LDesc.OpOK, LDesc.lv, LDesc.lp, LDesc.lc,
        hl0, hl, h1] <;> simpa [mkDesc, products, chains] using hc
  term_ok := by
    intro c hc t ht
    have hc' : c < 2 := by simpa [mkDesc, chains] using hc
    have h1 : 1 < 2 ^ b := Nat.one_lt_two_pow (by omega)
    interval_cases c <;> simp [mkDesc, chains] at ht <;>
      rcases ht with rfl | rfl | rfl <;>
      simp [LDesc.SrcOK, mkDesc, products, hl0, hl, h1, LDesc.lc]
  coeff_le := by
    intro ch hch
    simp [mkDesc, chains] at hch
    rcases hch with rfl | rfl <;> norm_num
  prod_once := by
    intro c hc c' hc' p hp hp'
    have hca : c < 2 := by simpa [mkDesc, chains] using hc
    have hcb : c' < 2 := by simpa [mkDesc, chains] using hc'
    interval_cases c <;> interval_cases c' <;>
      simp [mkDesc, chains, ChainD.HasProd] at hp hp' ⊢ <;> omega
  cmp_ok := by
    intro q hq
    change q < cs.length at hq
    have hm : cs.getD q default ∈ cs := by
      rw [List.getD_eq_getElem _ _ hq]
      exact List.getElem_mem hq
    obtain ⟨hv, ho⟩ := hcs _ hm
    refine ⟨hv, ?_⟩
    change (mkDesc cs).CmpOK b lk 0 (cs.getD q default).rhs
    cases he : (cs.getD q default).rhs with
    | var v =>
      rw [he] at ho
      simpa [LDesc.CmpOK, Operand.OK, mkDesc, LDesc.lv] using ho
    | const xs =>
      rw [he] at ho
      simpa [LDesc.CmpOK, Operand.OK, hl0] using ho

theorem comparisons_ok (b l0 : ℕ) :
    ∀ q ∈ comparisons b l0, q.v < 5 ∧ q.rhs.OK b l0 5 := by
  intro q hq
  simp [comparisons] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, toLimbs_OK b l0 2⟩
  · exact ⟨by norm_num, toLimbs_OK b l0 2⟩
  · norm_num [Operand.OK]
  · norm_num [Operand.OK]

theorem nodeDesc_WFB {b l0 : ℕ} (lk : ℕ → ℕ)
    (hb : 1 ≤ b) (hl : 1 ≤ l0) (hl0 : lk 0 = l0) : (nodeDesc b l0).WFB b lk :=
  mkDesc_WFB _ lk hb hl hl0 (comparisons_ok b l0)

theorem pinnedDesc_WFB {b l0 a c : ℕ} (lk : ℕ → ℕ)
    (hb : 1 ≤ b) (hl : 1 ≤ l0) (hl0 : lk 0 = l0) : (pinnedDesc b l0 a c).WFB b lk := by
  apply mkDesc_WFB _ lk hb hl hl0
  intro q hq
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl | rfl
  · exact comparisons_ok b l0 q hq
  · exact ⟨by norm_num, toLimbs_OK b l0 a⟩
  · exact ⟨by norm_num, toLimbs_OK b l0 c⟩

theorem nodeDesc_spread (b l0 : ℕ) : (nodeDesc b l0).Spread 5 where
  var := by intro v hv; simp [nodeDesc, mkDesc, LDesc.lv] at *; omega
  prod := by intro p hp; simp [nodeDesc, mkDesc, products, LDesc.lp, LDesc.lc] at *; omega
  chain := by intro c hc; simp [nodeDesc, mkDesc, chains, LDesc.lc] at *; omega
  cmp := by intro q hq; simp [nodeDesc, mkDesc, comparisons, LDesc.lq, LDesc.lv] at *; omega

theorem pinnedDesc_spread (b l0 a c : ℕ) : (pinnedDesc b l0 a c).Spread 6 where
  var := by intro v hv; simp [pinnedDesc, mkDesc, LDesc.lv] at *; omega
  prod := by intro p hp; simp [pinnedDesc, mkDesc, products, LDesc.lp, LDesc.lc] at *; omega
  chain := by intro j hj; simp [pinnedDesc, mkDesc, chains, LDesc.lc] at *; omega
  cmp := by intro q hq; simp [pinnedDesc, mkDesc, comparisons, LDesc.lq, LDesc.lv] at *; omega

def solutions (b l0 a c box : ℕ) : Finset (Fin 5 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 5 => range box).filter
    (fun x => (pinnedDesc b l0 a c).D.Sat b (extV 5 x))

theorem mem_solutions {b l0 a c box : ℕ} (h2 : 2 < 2 ^ (b * l0))
    (ha : a < 2 ^ (b * l0)) (hc : c < 2 ^ (b * l0)) (x : Fin 5 → ℕ) :
    x ∈ solutions b l0 a c box ↔
      (∀ v, x v < box) ∧ x 0 = a ∧ x 1 = c ∧ 2 ≤ a ∧ 2 ≤ c ∧
      x 2 = a * c ∧ Certificate a c (x 3) (x 4) := by
  simp [solutions, pinnedDesc_sat h2 ha hc, extV]

def encode (a c u v : ℕ) (j : Fin 5) : ℕ :=
  match j.val with
  | 0 => a
  | 1 => c
  | 2 => a * c
  | 3 => u
  | _ => v

theorem encode_mem {b l0 a c box u v : ℕ} (h2 : 2 < 2 ^ (b * l0))
    (ha : a < 2 ^ (b * l0)) (hc : c < 2 ^ (b * l0))
    (ha2 : 2 ≤ a) (hc2 : 2 ≤ c) (hbox : a * c < box) (hcert : Certificate a c u v) :
    encode a c u v ∈ solutions b l0 a c box := by
  rw [mem_solutions h2 ha hc]
  refine ⟨?_, rfl, rfl, ha2, hc2, rfl, hcert⟩
  intro j
  have hua := hcert.1
  have hva := hcert.2.1
  fin_cases j <;> simp [encode] <;> nlinarith

theorem assignment_eq_encode {b l0 a c box u v : ℕ} (h2 : 2 < 2 ^ (b * l0))
    (ha : a < 2 ^ (b * l0)) (hc : c < 2 ^ (b * l0))
    {x : Fin 5 → ℕ} (hx : x ∈ solutions b l0 a c box) (hcert : Certificate a c u v) :
    x = encode a c u v := by
  obtain ⟨_, hx0, hx1, _, hc2, hx2, hxcert⟩ := (mem_solutions h2 ha hc x).1 hx
  obtain ⟨hu, hv⟩ := hxcert.unique (by omega) hcert
  funext j
  fin_cases j <;> simp [encode] <;> omega

/-- The fiber over fixed A,B is literally a singleton, not merely equinumerous.
The product and both bounded Bezout variables introduce no multiplicity. -/
theorem solutions_eq_singleton {b l0 a c box u v : ℕ} (h2 : 2 < 2 ^ (b * l0))
    (ha : a < 2 ^ (b * l0)) (hc : c < 2 ^ (b * l0))
    (ha2 : 2 ≤ a) (hc2 : 2 ≤ c) (hbox : a * c < box) (hcert : Certificate a c u v) :
    solutions b l0 a c box = {encode a c u v} := by
  ext x
  rw [mem_singleton]
  constructor
  · intro hx
    exact assignment_eq_encode h2 ha hc hx hcert
  · rintro rfl
    exact encode_mem h2 ha hc ha2 hc2 hbox hcert

theorem solutions_eq_empty_of_not_coprime {b l0 a c box : ℕ}
    (h2 : 2 < 2 ^ (b * l0)) (ha : a < 2 ^ (b * l0)) (hc : c < 2 ^ (b * l0))
    (hnot : ¬a.Coprime c) : solutions b l0 a c box = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨_, _, _, _, _, _, hcert⟩ := (mem_solutions h2 ha hc x).1 hx
  exact hnot hcert.coprime

/-- The actual LDesc.countB of the pinned arithmetic node is the coprime indicator.
The common box need only contain the parent product A*B. -/
theorem pinnedDesc_count {b l0 a c : ℕ} (bx : ℕ → ℕ)
    (h2 : 2 < 2 ^ (b * l0)) (ha : a < 2 ^ (b * l0)) (hc : c < 2 ^ (b * l0))
    (ha2 : 2 ≤ a) (hc2 : 2 ≤ c) (hbox : a * c < bx 0) :
    (pinnedDesc b l0 a c).countB b bx = if a.Coprime c then 1 else 0 := by
  change (solutions b l0 a c (bx 0)).card = _
  by_cases hcop : a.Coprime c
  · obtain ⟨u, v, hcert⟩ := certificate_exists ha2 hc2 hcop
    rw [solutions_eq_singleton h2 ha hc ha2 hc2 hbox hcert]
    simp [hcop]
  · rw [solutions_eq_empty_of_not_coprime h2 ha hc hcop]
    simp [hcop]

end EthFollowup.Primes.CoprimeNode
