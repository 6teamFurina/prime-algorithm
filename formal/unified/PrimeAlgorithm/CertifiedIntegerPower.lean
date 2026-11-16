import PrimeAlgorithm.CertifiedRawGaussian
import ClauseBound.ParityChecks.CertLib

set_option maxHeartbeats 1500000

namespace PrimeAlgorithm.CertifiedIntegerPower

open Finset Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
  CertifiedGaussianRat

def unit (imag : Bool) (j : ℕ) : ℤ :=
  if imag then (if j % 4 = 1 then 1 else if j % 4 = 3 then -1 else 0)
  else (if j % 4 = 0 then 1 else if j % 4 = 2 then -1 else 0)

theorem unit_embed (j : ℕ) :
    (unit false j : ℂ) + (unit true j : ℂ) * Complex.I = Complex.I ^ j := by
  rw [Complex.I_pow_eq_pow_mod]
  have hj : j % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : j % 4 <;> norm_num [unit, h, Complex.I_pow_three]

def component (imag : Bool) (k : ℕ) (a b : ℤ) : ℤ :=
  ∑ j ∈ range (k + 1), a ^ j * b ^ (k - j) * (k.choose j : ℤ) * unit imag (k - j)

def power (k : ℕ) (a b : ℤ) : CertifiedCauchy.GaussianIntPair :=
  (component false k a b, component true k a b)

theorem power_embed (k : ℕ) (a b : ℤ) :
    (component false k a b : ℂ) + (component true k a b : ℂ) * Complex.I =
      ((a : ℂ) + (b : ℂ) * Complex.I) ^ k := by
  simp only [component, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [sum_mul, ← sum_add_distrib, add_pow]
  apply sum_congr rfl
  intro j _hj
  rw [mul_pow]
  calc
    _ = (a : ℂ) ^ j * (b : ℂ) ^ (k - j) * (k.choose j : ℂ) *
        ((unit false (k - j) : ℂ) + (unit true (k - j) : ℂ) * Complex.I) := by ring
    _ = _ := by rw [unit_embed]; ring

theorem list_sum_range (m : ℕ) (f : ℕ → ℤ) :
    ((List.range m).map f).sum = ∑ j ∈ range m, f j := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, sum_range_succ, ih]

theorem unit_polyT (imag : Bool) : PolyT (unit imag) := by
  unfold unit
  cases imag <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

theorem component_polyT {α : Type} [Enc α] (imag : Bool)
    {k : α → ℕ} {a b : α → ℤ} (hk : Unary k) (ha : PolyT a) (hb : PolyT b) :
    PolyT (fun x => component imag (k x) (a x) (b x)) := by
  have hK : Unary (fun p : α × ℕ => k p.1) := hk.comp PolyT.id'.fst
  have hJ : Unary (fun p : α × ℕ => min p.2 (k p.1 + 1)) :=
    unary_min_right PolyT.id'.snd (hK.add (Unary.const 1))
  have hD : Unary (fun p : α × ℕ => k p.1 - min p.2 (k p.1 + 1)) :=
    unary_sub hK hJ.poly
  have hA : PolyT (fun p : α × ℕ => a p.1 ^ min p.2 (k p.1 + 1)) :=
    powZ_polyT (ha.comp PolyT.id'.fst) hJ
  have hB : PolyT (fun p : α × ℕ => b p.1 ^ (k p.1 - min p.2 (k p.1 + 1))) :=
    powZ_polyT (hb.comp PolyT.id'.fst) hD
  have hC : PolyT (fun p : α × ℕ => (k p.1).choose (min p.2 (k p.1 + 1))) :=
    choose_polyT hK.poly hJ
  have hU : PolyT (fun p : α × ℕ => unit imag (k p.1 - min p.2 (k p.1 + 1))) :=
    (unit_polyT imag).comp hD.poly
  have hf : PolyT (fun p : α × ℕ =>
      a p.1 ^ min p.2 (k p.1 + 1) * b p.1 ^ (k p.1 - min p.2 (k p.1 + 1)) *
      ((k p.1).choose (min p.2 (k p.1 + 1)) : ℤ) *
      unit imag (k p.1 - min p.2 (k p.1 + 1))) := by fun_prop
  have hlist := map_range_polyT
    (f := fun x j => a x ^ j * b x ^ (k x - j) * ((k x).choose j : ℤ) * unit imag (k x - j))
    (hk.add (Unary.const 1)) hf
  exact (sumZ_polyT hlist).congr (fun x => list_sum_range _ _)

theorem power_polyT {α : Type} [Enc α] {k : α → ℕ} {a b : α → ℤ}
    (hk : Unary k) (ha : PolyT a) (hb : PolyT b) :
    PolyT (fun x => power (k x) (a x) (b x)) :=
  PolyT.prodMk (component_polyT false hk ha hb) (component_polyT true hk ha hb)

end PrimeAlgorithm.CertifiedIntegerPower
