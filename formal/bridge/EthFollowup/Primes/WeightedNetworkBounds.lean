/-
# Weighted bounds for ArithL without a spread hypothesis

The original `ArithL` network and its checks are unchanged.  This module packages the
description-weighted estimates already present in `aBSum_le'` and
`g_mul_card_inc_le'`, before their specialization to a fixed `Spread` constant.

* `numAW_le_A`: the number of wires is at most the weighted limb mass `A`;
* `arithSys_U_le`: total communication is at most `2 * Wa n * A n L`;
* `arithSys_is`: the network has parameters
  `P = 3 * ceil((Wa n * A n L) / g) + 3 * Wa n * D₀ n L + 1`, `B = 1`.

Only well-formedness is used for the node bound.  No spread or bound on the number
of levels is assumed.  Standard axioms only.
-/
import EthFollowup.Primes.ArithLNetCount
import Mathlib.Algebra.Order.Floor.Div

set_option linter.unusedSectionVars false

namespace EthFollowup.Primes.WeightedNetworkBounds

open Finset EthFollowup.ExactHC EthFollowup.Factoring EthFollowup.ModP

/-- The weighted limb mass occurring in the general stage-sum estimate. -/
def A (n : ℕ) (L : LDesc) : ℕ :=
  SV L (kl n) + 60 * SP L (kl n) + 8 * SC L (kl n) + 2 * SQ L (kl n)

/-- The additive stage overhead before multiplication by the common label width. -/
def D₀ (n : ℕ) (L : LDesc) : ℕ :=
  L.D.nV + 10 * L.D.nP + 2 * L.D.nC + 2 * L.D.nQ + 17 * SP L (kL1 n)

/-- Weighted communication mass in bits. -/
def T (n : ℕ) (L : LDesc) : ℕ := Wa n * A n L

/-- An integer node-load bound, with natural-number ceiling division. -/
def P (n : ℕ) (L : LDesc) (g : ℕ) : ℕ :=
  3 * (T n L ⌈/⌉ g) + 3 * Wa n * D₀ n L + 1

/-- Wire count bounded directly by the weighted description, with no `Spread`. -/
theorem numAW_le_A (n : ℕ) (L : LDesc) : numAW n L ≤ A n L := by
  rw [numAW_eq]
  simp only [sum_range_succ, sum_range_zero, zero_add, wObj,
    List.getD_cons_zero, List.getD_cons_succ, wBox,
    List.prod_cons, List.prod_nil, mul_one]
  have tP : ∑ p ∈ range L.D.nP, 2 * kl n (L.lp p) +
      ∑ p ∈ range L.D.nP, 2 * (kL1 n (L.lp p) * kl1 n (L.lp p)) +
      ∑ p ∈ range L.D.nP, 2 * (kL1 n (L.lp p) * kL1 n (L.lp p)) +
      ∑ p ∈ range L.D.nP, kL1 n (L.lp p) * kL1 n (L.lp p) +
      ∑ p ∈ range L.D.nP, kL1 n (L.lp p) * kL1 n (L.lp p) +
      ∑ p ∈ range L.D.nP, kL1 n (L.lp p) * kL1 n (L.lp p) =
        26 * SP L (kl n) := by
    unfold SP
    rw [mul_sum]
    simp only [← sum_add_distrib]
    exact sum_congr rfl fun p _ => by unfold kl; rw [kL1_eq]; ring
  have tC : ∑ j ∈ range L.D.nC, (kKc n (L.lc j) - 1) ≤ 4 * SC L (kl n) := by
    unfold SC
    rw [mul_sum]
    exact sum_le_sum fun j _ => by
      have : kKc n (L.lc j) ≤ 4 * kl n (L.lc j) := by
        unfold kKc kl
        rw [kL1_eq]
        nlinarith [one_le_kl1 n (L.lc j)]
      omega
  have tQ : ∑ q ∈ range L.D.nQ, (kl n (L.lq q) - 1) ≤ SQ L (kl n) :=
    sum_le_sum fun q _ => Nat.sub_le _ _
  unfold A SV
  omega

/-- The original stage-sum estimate, exposed with the weighted parameters. -/
theorem aBSum_le {n : ℕ} {L : LDesc} (hL : L.WF n) (g : ℕ) :
    aBSum n L g ≤ A n L + g * D₀ n L :=
  aBSum_le' hL g

/-- Total communication bounded by the actual weighted mass, without `Spread`. -/
theorem arithSys_U_le {n : ℕ} {L : LDesc} {g : ℕ} (hg : 2 ≤ g) :
    ((arithSys n L g hg).net (aLabCode n)).U ≤ 2 * Wa n * A n L := by
  rw [LabelSystem.U_eq, Fintype.card_fin, Fintype.card_eq_zero, clog_Wa, add_zero]
  have h := Nat.mul_le_mul_right (Wa n) (numAW_le_A n L)
  calc
    2 * (numAW n L * Wa n) ≤ 2 * (A n L * Wa n) := Nat.mul_le_mul_left 2 h
    _ = 2 * Wa n * A n L := by ring

/-- The bit load at each node for the unchanged ArithL clustering. -/
theorem card_inc_mul_Wa_le {n : ℕ} {L : LDesc} {g : ℕ}
    (hg : 2 ≤ g) (hL : L.WF n) (a : Fin g) :
    #(univ.filter ((arithSys n L g hg).Inc a)) * Wa n ≤ P n L g := by
  set X := #(univ.filter ((arithSys n L g hg).Inc a))
  have h1 := g_mul_card_inc_le' (n := n) (L := L) hg a
  have h2 := aBSum_le hL g
  have h3 : g * (X * Wa n) ≤ 3 * T n L + g * (3 * Wa n * D₀ n L) := by
    have h := Nat.mul_le_mul_right (Wa n)
      (h1.trans (Nat.mul_le_mul_left 3 h2))
    dsimp [X, T]
    nlinarith
  have hceil : T n L ≤ g * (T n L ⌈/⌉ g) :=
    (ceilDiv_le_iff_le_mul (by omega : 0 < g)).1 le_rfl
  have h4 : g * (X * Wa n) ≤
      g * (3 * (T n L ⌈/⌉ g) + 3 * Wa n * D₀ n L) := by
    nlinarith
  change X * Wa n ≤ P n L g
  unfold P
  nlinarith

/-- Definition 2 with the weighted node bound and coefficient bound 1. -/
theorem arithSys_is {n : ℕ} {L : LDesc} {g : ℕ}
    (hg : 2 ≤ g) (hL : L.WF n) :
    ((arithSys n L g hg).net (aLabCode n)).Is (P n L g) 1 := by
  refine LabelSystem.net_is _ _ ?_ le_rfl (fun a => ?_)
    (fun a ℓ y => by rw [arithSys_T]; exact arithT_abs_lt (n := n) (L := L) a ℓ)
  · unfold P
    omega
  · rw [arithSys_touch hg, add_zero, clog_Wa]
    exact card_inc_mul_Wa_le hg hL a

end EthFollowup.Primes.WeightedNetworkBounds
