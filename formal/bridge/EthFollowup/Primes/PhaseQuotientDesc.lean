/-
A real ArithL descriptor for a nonnegative rational-kernel quotient.
Variables: numerator A, denominator D, quotient q, remainder r, weight witness w.
The equations are A = D*q+r, 0<=r<D, 1<=D, 0<=w<q.
Thus, with A,D pinned, its exact count is floor(A/D), including a zero quotient.
-/
import EthFollowup.Primes.ArithLDesc
import EthFollowup.ModP.ArithInstances
import EthFollowup.Primes.WeightedNetworkBounds
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace EthFollowup.Primes.PhaseQuotient

open Finset EthFollowup.ModP

def products : List ProdD :=
  [⟨0, .const [1]⟩, ⟨1, .var 2⟩, ⟨3, .const [1]⟩]

def chains : List ChainD :=
  [⟨[⟨1, .prod 0⟩], [⟨1, .prod 1⟩, ⟨1, .prod 2⟩]⟩]

def mkDesc (cs : List CmpD) : LDesc where
  D := { nV := 5, pat := [], prods := products, chains := chains, cmps := cs }
  lev := []
  levC := []

def comparisons : List CmpD :=
  [⟨1, .const [1], .ge⟩, ⟨3, .var 1, .lt⟩, ⟨4, .var 2, .lt⟩]

def nodeDesc : LDesc := mkDesc comparisons

def pinnedDesc (b l0 A D : ℕ) : LDesc := mkDesc (comparisons ++
  [⟨0, .const (toLimbs b l0 A), .eq⟩, ⟨1, .const (toLimbs b l0 D), .eq⟩])

theorem nodeDesc_sat (b : ℕ) (x : ℕ → ℕ) :
    nodeDesc.D.Sat b x ↔
      1 ≤ x 1 ∧ x 3 < x 1 ∧ x 4 < x 2 ∧ x 0 = x 1 * x 2 + x 3 := by
  simp [nodeDesc, mkDesc, comparisons, Desc.Sat, patMatch, CmpRel.Holds,
    Operand.eval, products, chains, sideVal, Src.eval, ProdD.eval,
    show limbsVal b [1] = 1 by simp [limbsVal]]
  tauto

theorem pinnedDesc_sat {b l0 A D : ℕ}
    (hA : A < 2^(b*l0)) (hD : D < 2^(b*l0)) (x : ℕ → ℕ) :
    (pinnedDesc b l0 A D).D.Sat b x ↔
      x 0 = A ∧ x 1 = D ∧ 1 ≤ x 1 ∧ x 3 < x 1 ∧ x 4 < x 2 ∧
        x 0 = x 1 * x 2 + x 3 := by
  simp [pinnedDesc, mkDesc, comparisons, Desc.Sat, patMatch, CmpRel.Holds,
    Operand.eval, limbsVal_toLimbs hA, limbsVal_toLimbs hD,
    products, chains, sideVal, Src.eval, ProdD.eval,
    show limbsVal b [1] = 1 by simp [limbsVal]]
  tauto

theorem mkDesc_WFB {b l0 : ℕ} (cs : List CmpD) (lk : ℕ → ℕ)
    (hb : 1 ≤ b) (hl : 1 ≤ l0) (hl0 : lk 0 = l0)
    (hcs : ∀ q ∈ cs, q.v < 5 ∧ q.rhs.OK b l0 5) : (mkDesc cs).WFB b lk where
  pat_len := by intro v hv; simp [mkDesc]
  prod_ok := by
    intro p hp
    have hp' : p < 3 := by simpa [mkDesc, products] using hp
    have hc : (mkDesc cs).D.chainOf p < 1 := by
      change (chains.findIdx fun ch => decide (ch.HasProd p)) < 1
      interval_cases p <;> decide
    have h1 : 1 < 2^b := Nat.one_lt_two_pow (by omega)
    interval_cases p <;>
      simp [mkDesc, products, chains, LDesc.OpOK, LDesc.lv, LDesc.lp, LDesc.lc,
        hl0, hl, h1] <;> simpa [mkDesc, products, chains] using hc
  term_ok := by
    intro c hc t ht
    have hc' : c = 0 := by simpa [mkDesc, chains] using hc
    subst c
    simp [mkDesc, chains] at ht
    rcases ht with rfl | rfl | rfl <;>
      norm_num [LDesc.SrcOK, mkDesc, products]
  coeff_le := by
    intro ch hch
    simp [mkDesc, chains] at hch
    rcases hch with rfl
    norm_num
  prod_once := by
    intro c hc c' hc' p hp hp'
    have : c < 1 := by simpa [mkDesc, chains] using hc
    have : c' < 1 := by simpa [mkDesc, chains] using hc'
    omega
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

theorem comparisons_ok {b l0 : ℕ} (hb : 1 ≤ b) (hl : 1 ≤ l0) :
    ∀ q ∈ comparisons, q.v < 5 ∧ q.rhs.OK b l0 5 := by
  intro q hq
  simp [comparisons] at hq
  rcases hq with rfl | rfl | rfl
  · have h1 : 1 < 2^b := Nat.one_lt_two_pow (by omega)
    simp [Operand.OK, hl, h1]
  · norm_num [Operand.OK]
  · norm_num [Operand.OK]

theorem pinnedDesc_WFB {b l0 A D : ℕ} (lk : ℕ → ℕ)
    (hb : 1 ≤ b) (hl : 1 ≤ l0) (hl0 : lk 0 = l0) :
    (pinnedDesc b l0 A D).WFB b lk := by
  apply mkDesc_WFB _ lk hb hl hl0
  intro q hq
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | rfl | rfl
  · exact comparisons_ok hb hl _ hq
  · exact ⟨by norm_num, toLimbs_OK b l0 A⟩
  · exact ⟨by norm_num, toLimbs_OK b l0 D⟩

theorem pinnedDesc_spread (b l0 A D : ℕ) : (pinnedDesc b l0 A D).Spread 5 where
  var := by intro v hv; simp [pinnedDesc, mkDesc, LDesc.lv] at *; omega
  prod := by intro p hp; simp [pinnedDesc, mkDesc, products, LDesc.lp, LDesc.lc] at *; omega
  chain := by intro c hc; simp [pinnedDesc, mkDesc, chains, LDesc.lc] at *; omega
  cmp := by intro q hq; simp [pinnedDesc, mkDesc, comparisons, LDesc.lq, LDesc.lv] at *; omega

def encode (A D w : ℕ) (j : Fin 5) : ℕ :=
  match j.val with
  | 0 => A
  | 1 => D
  | 2 => A / D
  | 3 => A % D
  | _ => w

def solutions (b l0 A D box : ℕ) : Finset (Fin 5 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 5 => range box).filter
    fun x => (pinnedDesc b l0 A D).D.Sat b (extV 5 x)

theorem mem_solutions {b l0 A D box : ℕ}
    (hA : A < 2^(b*l0)) (hD : D < 2^(b*l0)) (x : Fin 5 → ℕ) :
    x ∈ solutions b l0 A D box ↔
      (∀ v, x v < box) ∧ x 0 = A ∧ x 1 = D ∧ 1 ≤ x 1 ∧
        x 3 < x 1 ∧ x 4 < x 2 ∧ x 0 = x 1 * x 2 + x 3 := by
  simp [solutions, pinnedDesc_sat hA hD, extV]

private theorem quotient_unique {A D q r : ℕ} (_hD : 0 < D)
    (hr : r < D) (he : A = D*q+r) : q = A/D ∧ r = A%D := by
  have hq : A/D = q := Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  refine ⟨hq.symm, ?_⟩
  have := Nat.div_add_mod A D
  nlinarith

/-- The actual descriptor count is the quotient weight, not a Boolean test. -/
theorem pinnedDesc_count {b l0 A D : ℕ} (bx : ℕ → ℕ)
    (hA : A < 2^(b*l0)) (hD : D < 2^(b*l0)) (hDpos : 0 < D)
    (hboxA : A < bx 0) (hboxD : D < bx 0) :
    (pinnedDesc b l0 A D).countB b bx = A/D := by
  change (solutions b l0 A D (bx 0)).card = _
  rw [← card_range (A/D)]
  apply card_nbij (fun x : Fin 5 → ℕ => x 4)
  · intro x hx
    obtain ⟨_, hx0, hx1, _, hr, hw, he⟩ := (mem_solutions hA hD x).1 hx
    have hqr := quotient_unique hDpos (by simpa [hx1] using hr) (by simpa [hx0,hx1] using he)
    change x 4 ∈ range (A/D)
    exact mem_range.mpr (hqr.1 ▸ hw)
  · intro x hx y hy he
    obtain ⟨_, hx0, hx1, _, hr, hw, hx⟩ := (mem_solutions hA hD x).1 hx
    obtain ⟨_, hy0, hy1, _, hr', hw', hy⟩ := (mem_solutions hA hD y).1 hy
    have hxqr := quotient_unique hDpos (by simpa [hx1] using hr) (by simpa [hx0,hx1] using hx)
    have hyqr := quotient_unique hDpos (by simpa [hy1] using hr') (by simpa [hy0,hy1] using hy)
    change x 4 = y 4 at he
    funext j
    fin_cases j <;> simp_all
  · intro w hw
    refine ⟨encode A D w, ?_, rfl⟩
    change encode A D w ∈ solutions b l0 A D (bx 0)
    rw [mem_solutions hA hD]
    have hw' : w < A/D := mem_range.mp hw
    have hq := Nat.div_le_self A D
    have hr := Nat.mod_lt A hDpos
    refine ⟨?_, rfl, rfl, hDpos, hr, hw', ?_⟩
    · intro j
      fin_cases j <;> simp [encode] <;> omega
    · simpa [encode, Nat.mul_comm] using (Nat.div_add_mod A D).symm


/-- Free-input version, ready to be wired into larger constant-arity constraints. -/
theorem nodeDesc_WFB {b l0 : ℕ} (lk : ℕ → ℕ)
    (hb : 1 ≤ b) (hl : 1 ≤ l0) (hl0 : lk 0 = l0) : nodeDesc.WFB b lk :=
  mkDesc_WFB comparisons lk hb hl hl0 (comparisons_ok hb hl)

theorem nodeDesc_spread : nodeDesc.Spread 5 where
  var := by intro v hv; simp [nodeDesc, mkDesc, LDesc.lv] at *; omega
  prod := by intro p hp; simp [nodeDesc, mkDesc, products, LDesc.lp, LDesc.lc] at *; omega
  chain := by intro c hc; simp [nodeDesc, mkDesc, chains, LDesc.lc] at *; omega
  cmp := by intro q hq; simp [nodeDesc, mkDesc, comparisons, LDesc.lq, LDesc.lv] at *; omega

open EthFollowup.Factoring EthFollowup.ExactHC

def actualDesc (n A D : ℕ) : LDesc := pinnedDesc (b n) (kl n 0) A D

theorem actualDesc_WF (n A D : ℕ) : (actualDesc n A D).WF n :=
  pinnedDesc_WFB (kl n) (one_le_b n) (kl_pos n 0) rfl

/-- The existing arithmetic-network construction has exactly the quotient value. -/
theorem actualNetwork_value {n g A D : ℕ} (hg : 2 ≤ g)
    (hA : A < lbox n 0) (hD : D < lbox n 0) (hDpos : 0 < D) :
    ((arithSys n (actualDesc n A D) g hg).net (aLabCode n)).value = (A/D : ℕ) := by
  rw [arithNet_value hg (actualDesc_WF n A D)]
  congr 1
  exact pinnedDesc_count (lbox n) hA hD hDpos hA hD

/-- The constructed quotient network satisfies the engine's actual size conditions. -/
theorem actualNetwork_is {n g A D : ℕ} (hg : 2 ≤ g) :
    ((arithSys n (actualDesc n A D) g hg).net (aLabCode n)).Is
      (WeightedNetworkBounds.P n (actualDesc n A D) g) 1 :=
  WeightedNetworkBounds.arithSys_is hg (actualDesc_WF n A D)

end EthFollowup.Primes.PhaseQuotient
