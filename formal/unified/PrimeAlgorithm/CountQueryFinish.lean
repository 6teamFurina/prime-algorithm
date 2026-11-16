import PrimeAlgorithm.CertifiedGenerator
import PrimeAlgorithm.PrimeCountInteger
import PrimeAlgorithm.IntegerCountQueryFinal

set_option maxHeartbeats 1500000

namespace PrimeAlgorithm.CountQueryFinish

open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
  CertifiedCauchy CertifiedGenerator CertifiedPrimeSum PrimeCountInteger

open IntegerPrimeSum (commonScale)

abbrev Item := List Bool × ℤ
abbrev Input := List Bool × List ℕ

/-- Signed coefficients are carried by the query list; the counting answers
are nonnegative integers in the same list order. -/
def dot (items : List Item) (counts : List ℕ) : ℤ :=
  (List.zipWith (fun (q : Item) (c : ℕ) => q.2 * (c : ℤ)) items counts).sum

def result (b : ℕ) (numerator : ℤ) : ℤ :=
  (2 * numerator + (commonScale b : ℤ) ^ 4) / (2 * (commonScale b : ℤ) ^ 4)

def finish (b : List Bool → ℕ) (items : List Bool → List Item) (p : Input) : List Bool :=
  Nat.bits (result (b p.1) (dot (items p.1) p.2)).toNat

theorem dot_map (items : List Item) (count : Item → ℕ) :
    dot items (items.map count) = (items.map (fun q => q.2 * (count q : ℤ))).sum := by
  simp only [dot, List.zipWith_map_right, List.zipWith_self]

theorem dot_map_count (items : List Item) (count : List Bool → ℕ) :
    dot items (items.map (fun q => count q.1)) =
      (items.map (fun q => q.2 * (count q.1 : ℤ))).sum := dot_map _ _

@[fun_prop] theorem dot_polyT {α : Type} [Enc α]
    {items : α → List Item} {counts : α → List ℕ}
    (hi : PolyT items) (hc : PolyT counts) : PolyT (fun x => dot (items x) (counts x)) := by
  have hz := PolyT.zip hi hc
  have hm : PolyT (fun x => ((items x).zip (counts x)).map
      (fun q : Item × ℕ => q.1.2 * (q.2 : ℤ))) :=
    PolyT.map (f := fun (_ : α) (q : Item × ℕ) => q.1.2 * (q.2 : ℤ)) (by fun_prop) hz
  exact (sumZ_polyT hm).congr (fun x => by
    rw [List.map_zip_eq_zipWith]
    rfl)

theorem commonScale_polyT {α : Type} [Enc α] {b : α → ℕ} (hb : Unary b) :
    PolyT (fun x => commonScale (b x)) := by
  have hp := coefficientBits_unary hb
  have ht : Unary (fun x => reciprocalBits (b x)) := by
    unfold reciprocalBits Cauchy.dyadicBits
    fun_prop
  exact PolyT.mul (nodeCount_unary hb).poly (PolyT.two_pow (hp.add ht))

@[fun_prop] theorem result_polyT {α : Type} [Enc α] {b : α → ℕ} {z : α → ℤ}
    (hb : Unary b) (hz : PolyT z) : PolyT (fun x => result (b x) (z x)) := by
  have hs := commonScale_polyT hb
  have hp : PolyT (fun x => (commonScale (b x) : ℤ) ^ 4) :=
    powZ_polyT (PolyT.natCast hs) (Unary.const 4)
  have hn : PolyT (fun x => 2 * z x + (commonScale (b x) : ℤ) ^ 4) :=
    PolyT.addZ (PolyT.mulZ (PolyT.const 2) hz) hp
  have hd : PolyT (fun x => 2 * commonScale (b x) ^ 4) :=
    PolyT.mul (PolyT.const 2) (PolyT.pow_unary hs (Unary.const 4))
  exact (divZ_polyT hn hd).congr (fun x => by simp only [result, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_pow])

theorem finish_polyT {b : List Bool → ℕ} {items : List Bool → List Item}
    (hb : Unary b) (hi : PolyT items) : PolyT (finish b items) := by
  have hB : Unary (fun p : Input => b p.1) := hb.comp PolyT.id'.fst
  have hI : PolyT (fun p : Input => items p.1) := hi.comp PolyT.id'.fst
  have hD := dot_polyT hI (PolyT.id'.snd : PolyT (fun p : Input => p.2))
  exact PolyT.bits (PolyT.toNat (result_polyT hB hD))

theorem result_eq_integerResult {b N : ℕ} {D : PrimeData} {z : ℤ}
    (hz : z = (integerPrimeCount b D N).1) : result b z = integerResult b D N := by
  rw [hz]
  rfl

theorem finish_eq_integerResult {b : List Bool → ℕ} {items : List Bool → List Item}
    (w : List Bool) (counts : List ℕ) (D : PrimeData) (N : ℕ)
    (hnum : dot (items w) counts = (integerPrimeCount (b w) D N).1) :
    finish b items (w, counts) = Nat.bits (integerResult (b w) D N).toNat := by
  unfold finish
  rw [result_eq_integerResult hnum]

theorem finish_eq_primeCounting {b : List Bool → ℕ} {items : List Bool → List Item}
    (w : List Bool) (counts : List ℕ) (D : PrimeData) (N : ℕ)
    (hnum : dot (items w) counts = (integerPrimeCount (b w) D N).1)
    (hN : N ≤ 2 ^ b w) (hD : Certified (b w) D) :
    finish b items (w, counts) = Nat.bits (Nat.primeCounting N) := by
  rw [finish_eq_integerResult w counts D N hnum, integerResult_eq_primeCounting hN hD,
    Int.toNat_natCast]

theorem finish_eq_queryResult {b : List Bool → ℕ} {items : List Bool → List Item}
    (w : List Bool) (counts : List ℕ) (D : PrimeData) (N : ℕ)
    (hnum : dot (items w) counts = (IntegerCountQueryFinal.queryNumerator (b w) N D).re) :
    finish b items (w, counts) = Nat.bits (IntegerCountQueryFinal.queryResult (b w) N D).toNat := by
  unfold finish
  rw [hnum]
  rfl

theorem finish_queries_eq_primeCounting {b : List Bool → ℕ} {items : List Bool → List Item}
    (w : List Bool) (counts : List ℕ) (D : PrimeData) (N : ℕ)
    (hnum : dot (items w) counts = (IntegerCountQueryFinal.queryNumerator (b w) N D).re)
    (hN : N ≤ 2 ^ b w) (hD : Certified (b w) D) :
    finish b items (w, counts) = Nat.bits (Nat.primeCounting N) := by
  rw [finish_eq_queryResult w counts D N hnum,
    IntegerCountQueryFinal.queryResult_eq_primeCounting hN hD, Int.toNat_natCast]

end PrimeAlgorithm.CountQueryFinish
