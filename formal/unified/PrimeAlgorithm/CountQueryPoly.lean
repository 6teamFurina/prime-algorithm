import PrimeAlgorithm.CountQueryBounds
import PrimeAlgorithm.CertifiedGenerator

/-! The concrete certified coefficient generator supplies the actual query reader
in polynomial time. Index and branch choices are the finite outer-loop inputs. -/
namespace PrimeAlgorithm.CountQueryPoly
open Groundwork CertifiedCauchy CertifiedPrimeSum CountQueryExpansion CertifiedGenerator
  EthFollowup.Primes.CountKernel

variable {α : Type} [Enc α]

theorem reciprocalBits_unary {b : α → ℕ} (hb : Unary b) :
    Unary (fun x => reciprocalBits (b x)) := by
  unfold reciprocalBits Cauchy.dyadicBits
  exact ((Unary.const 7).mul hb).add (Unary.const 25)

/-- No evaluation of a transcendental constant occurs in the machine: these are
exact integer query encodings produced by the proved rational generator. -/
theorem generated_query_polyT {b N jM jN : α → ℕ}
    {indices : (x : α) → NodeChoices (b x)} {σ : α → Fin 4 → Bool} {unitD : α → Bool}
    (hb : Unary b) (hM : Unary jM) (hN : Unary jN)
    (hj : ∀k,PolyT fun x => ((indices x) k).1.val)
    (hi : ∀k,PolyT fun x => ((indices x) k).2)
    (hs : ∀k,PolyT fun x => σ x k) (hu : PolyT unitD) :
    PolyT fun x => query (parameters (b x) (N x) (jM x) (jN x)
      (generate (b x)) (indices x)) (queryBranch (unitD x) (indices x) (σ x)) := by
  have hp (k : Fin 4) := pole_polyT hb (hj k)
  apply query_polyT
  · exact PolyT.two_pow hM
  · exact PolyT.two_pow hN
  · exact PolyT.two_pow (reciprocalBits_unary hb)
  · intro k; exact PolyT.toNat (PolyT.fst (hp k))
  · intro k; exact PolyT.natAbs (PolyT.snd (hp k))
  · intro k; exact PolyT.two_pow (coefficientBits_unary hb)
  · exact hu
  · exact hs
  · exact hi

end PrimeAlgorithm.CountQueryPoly
