import PrimeAlgorithm.CertifiedRawPi
import PrimeAlgorithm.CertifiedNearest
import PrimeAlgorithm.CertifiedPrimeSum
import PrimeAlgorithm.CertifiedAnalyticBounds
import PrimeAlgorithm.CertifiedAnalyticStability

set_option maxHeartbeats 1500000

namespace PrimeAlgorithm.CertifiedGenerator

open Groundwork CertifiedRawGaussian CertifiedRawTaylor CertifiedRawPi
  CertifiedNearest CertifiedGaussianRat CertifiedCauchy CertifiedPrimeSum

/-- Extra guard bits cover analytic stability and the bounded amplitudes. -/
def order (b : ℕ) : ℕ := coefficientBits b + b + 256
def expOrder (b : ℕ) : ℕ := 31 + order b
def logOrder (b : ℕ) : ℕ := 4 * order b + 1

def rawExp (b : ℕ) (z : Raw) : Raw := polynomial false (expOrder b) z
def rawLogTwo (b : ℕ) : Raw := neg (polynomial true (logOrder b) (-1, 0, 2))
def rawLog (b : ℕ) (z : Raw) : Raw :=
  add (rawLogTwo b) (polynomial true (logOrder b) (add (mul z (1, 0, 2)) (ofInt (-1))))
def rawAngle (b : ℕ) : Raw := mul (pi (order b)) (0, 2, 1)
def rawNode (b j : ℕ) : Raw :=
  add (3, 0, 2) (mul (3, 0, 4)
    (rawExp b (mul (rawAngle b) (j, 0, nodeCount b))))
def rawLogAmplitude (b l j : ℕ) : Raw :=
  add (mul (ofInt l) (rawLogTwo b)) (rawLog b (rawNode b j))
def rawPhase (b j : ℕ) : Raw :=
  rawExp b (mul (rawAngle b) (add (rawNode b j) (ofInt (-1))))
def rawResidue (b j : ℕ) (f : Raw) : Raw :=
  mul f (add (rawNode b j) (-3, 0, 2))

def pole (b j : ℕ) : GaussianIntPair := nearest (coefficientBits b) (rawNode b j)
def logResidue (b l j : ℕ) : GaussianIntPair :=
  nearest (coefficientBits b) (rawResidue b j (rawLogAmplitude b l j))
def invLogResidue (b l j : ℕ) : GaussianIntPair :=
  nearest (coefficientBits b) (rawResidue b j (inv (rawLogAmplitude b l j)))
def phaseResidue (b j : ℕ) : GaussianIntPair :=
  nearest (coefficientBits b) (rawResidue b j (rawPhase b j))

def generate (b : ℕ) : PrimeData :=
  ⟨pole b, logResidue b, invLogResidue b, phaseResidue b⟩

theorem rawExp_valid (b : ℕ) {z : Raw} (hz : Valid z) : Valid (rawExp b z) :=
  polynomial_valid _ _ hz
theorem rawLogTwo_valid (b : ℕ) : Valid (rawLogTwo b) :=
  valid_neg (polynomial_valid _ _ (by norm_num [Valid]))
theorem rawLog_valid (b : ℕ) {z : Raw} (hz : Valid z) : Valid (rawLog b z) :=
  valid_add (rawLogTwo_valid b)
    (polynomial_valid _ _ (valid_add (valid_mul hz (by norm_num [Valid])) (valid_ofInt _)))
theorem rawAngle_valid (b : ℕ) : Valid (rawAngle b) :=
  valid_mul (pi_valid _) (by norm_num [Valid])
theorem rawNode_valid (b j : ℕ) : Valid (rawNode b j) :=
  valid_add (by norm_num [Valid]) (valid_mul (by norm_num [Valid])
    (rawExp_valid _ (valid_mul (rawAngle_valid b) (Cauchy.primeNodes_pos _))))
theorem rawLogAmplitude_valid (b l j : ℕ) : Valid (rawLogAmplitude b l j) :=
  valid_add (valid_mul (valid_ofInt _) (rawLogTwo_valid _))
    (rawLog_valid _ (rawNode_valid _ _))
theorem rawPhase_valid (b j : ℕ) : Valid (rawPhase b j) :=
  rawExp_valid _ (valid_mul (rawAngle_valid _) (valid_add (rawNode_valid _ _) (valid_ofInt _)))
theorem rawResidue_valid (b j : ℕ) {f : Raw} (hf : Valid f) : Valid (rawResidue b j f) :=
  valid_mul hf (valid_add (rawNode_valid _ _) (by norm_num [Valid]))

@[fun_prop] theorem coefficientBits_unary {α : Type} [Enc α] {b : α → ℕ}
    (hb : Unary b) : Unary (fun x => coefficientBits (b x)) := by
  unfold coefficientBits Cauchy.dyadicBits
  fun_prop
@[fun_prop] theorem nodeCount_unary {α : Type} [Enc α] {b : α → ℕ}
    (hb : Unary b) : Unary (fun x => nodeCount (b x)) := by
  unfold nodeCount Cauchy.primeNodes
  fun_prop
@[fun_prop] theorem order_unary {α : Type} [Enc α] {b : α → ℕ}
    (hb : Unary b) : Unary (fun x => order (b x)) := by unfold order; fun_prop
@[fun_prop] theorem expOrder_unary {α : Type} [Enc α] {b : α → ℕ}
    (hb : Unary b) : Unary (fun x => expOrder (b x)) := by unfold expOrder; fun_prop
@[fun_prop] theorem logOrder_unary {α : Type} [Enc α] {b : α → ℕ}
    (hb : Unary b) : Unary (fun x => logOrder (b x)) := by unfold logOrder; fun_prop

@[fun_prop] theorem ofInt_apply_polyT {α : Type} [Enc α] {n : α → ℤ}
    (hn : PolyT n) : PolyT (fun x => ofInt (n x)) :=
  PolyT.prodMk hn (PolyT.const (0, 1))

@[fun_prop] theorem rawExp_polyT {α : Type} [Enc α] {b : α → ℕ} {z : α → Raw}
    (hb : Unary b) (hz : PolyT z) : PolyT (fun x => rawExp (b x) (z x)) :=
  polynomial_polyT false (expOrder_unary hb) hz
@[fun_prop] theorem rawLogTwo_polyT {α : Type} [Enc α] {b : α → ℕ}
    (hb : Unary b) : PolyT (fun x => rawLogTwo (b x)) :=
  neg_apply_polyT (polynomial_polyT true (logOrder_unary hb) (PolyT.const (-1, 0, 2)))
@[fun_prop] theorem rawLog_polyT {α : Type} [Enc α] {b : α → ℕ} {z : α → Raw}
    (hb : Unary b) (hz : PolyT z) : PolyT (fun x => rawLog (b x) (z x)) :=
  add_apply_polyT (rawLogTwo_polyT hb) (polynomial_polyT true (logOrder_unary hb)
    (add_apply_polyT (mul_apply_polyT hz (PolyT.const (1, 0, 2))) (PolyT.const (ofInt (-1)))))
@[fun_prop] theorem rawAngle_polyT {α : Type} [Enc α] {b : α → ℕ}
    (hb : Unary b) : PolyT (fun x => rawAngle (b x)) :=
  mul_apply_polyT (pi_polyT (order_unary hb)) (PolyT.const (0, 2, 1))
@[fun_prop] theorem rawNode_polyT {α : Type} [Enc α] {b j : α → ℕ}
    (hb : Unary b) (hj : PolyT j) : PolyT (fun x => rawNode (b x) (j x)) :=
  add_apply_polyT (PolyT.const (3, 0, 2)) (mul_apply_polyT (PolyT.const (3, 0, 4))
    (rawExp_polyT hb (mul_apply_polyT (rawAngle_polyT hb)
      (PolyT.prodMk (PolyT.natCast hj) (PolyT.prodMk (PolyT.const 0) (nodeCount_unary hb).poly)))))
@[fun_prop] theorem rawLogAmplitude_polyT {α : Type} [Enc α] {b l j : α → ℕ}
    (hb : Unary b) (hl : PolyT l) (hj : PolyT j) :
    PolyT (fun x => rawLogAmplitude (b x) (l x) (j x)) :=
  add_apply_polyT (mul_apply_polyT (ofInt_apply_polyT (PolyT.natCast hl)) (rawLogTwo_polyT hb))
    (rawLog_polyT hb (rawNode_polyT hb hj))
@[fun_prop] theorem rawPhase_polyT {α : Type} [Enc α] {b j : α → ℕ}
    (hb : Unary b) (hj : PolyT j) : PolyT (fun x => rawPhase (b x) (j x)) :=
  rawExp_polyT hb (mul_apply_polyT (rawAngle_polyT hb)
    (add_apply_polyT (rawNode_polyT hb hj) (PolyT.const (ofInt (-1)))))
@[fun_prop] theorem rawResidue_polyT {α : Type} [Enc α] {b j : α → ℕ} {f : α → Raw}
    (hb : Unary b) (hj : PolyT j) (hf : PolyT f) :
    PolyT (fun x => rawResidue (b x) (j x) (f x)) :=
  mul_apply_polyT hf (add_apply_polyT (rawNode_polyT hb hj) (PolyT.const (-3, 0, 2)))

theorem pole_polyT {α : Type} [Enc α] {b j : α → ℕ}
    (hb : Unary b) (hj : PolyT j) : PolyT (fun x => pole (b x) (j x)) :=
  nearest_polyT (coefficientBits_unary hb) (rawNode_polyT hb hj)
theorem logResidue_polyT {α : Type} [Enc α] {b l j : α → ℕ}
    (hb : Unary b) (hl : PolyT l) (hj : PolyT j) : PolyT (fun x => logResidue (b x) (l x) (j x)) :=
  nearest_polyT (coefficientBits_unary hb)
    (rawResidue_polyT hb hj (rawLogAmplitude_polyT hb hl hj))
theorem invLogResidue_polyT {α : Type} [Enc α] {b l j : α → ℕ}
    (hb : Unary b) (hl : PolyT l) (hj : PolyT j) : PolyT (fun x => invLogResidue (b x) (l x) (j x)) :=
  nearest_polyT (coefficientBits_unary hb)
    (rawResidue_polyT hb hj (inv_apply_polyT (rawLogAmplitude_polyT hb hl hj)))
theorem phaseResidue_polyT {α : Type} [Enc α] {b j : α → ℕ}
    (hb : Unary b) (hj : PolyT j) : PolyT (fun x => phaseResidue (b x) (j x)) :=
  nearest_polyT (coefficientBits_unary hb) (rawResidue_polyT hb hj (rawPhase_polyT hb hj))

end PrimeAlgorithm.CertifiedGenerator
