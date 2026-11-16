import PrimeAlgorithm.CertifiedIntegerPower

set_option maxHeartbeats 1500000

namespace PrimeAlgorithm.CertifiedRawTaylor

open Finset Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
  CertifiedRawGaussian CertifiedIntegerPower CertifiedGaussianRat

/-- Every Taylor denominator divides m!, so a single common denominator
avoids rational normalization inside the finite sum. -/
def weight (isLog : Bool) (m k : ℕ) : ℤ :=
  if isLog then
    if k = 0 then 0 else (-1 : ℤ) ^ (k + 1) * (m.factorial / k : ℕ)
  else (m.factorial / k.factorial : ℕ)

def numerator (isLog imag : Bool) (m : ℕ) (z : Raw) : ℤ :=
  ∑ k ∈ range m,
    component imag k z.1 z.2.1 * (z.2.2 : ℤ) ^ (m - k) * weight isLog m k

def denominator (m : ℕ) (z : Raw) : ℕ := m.factorial * z.2.2 ^ m

def polynomial (isLog : Bool) (m : ℕ) (z : Raw) : Raw :=
  (numerator isLog false m z, numerator isLog true m z, denominator m z)

theorem polynomial_valid (isLog : Bool) (m : ℕ) {z : Raw} (hz : Valid z) :
    Valid (polynomial isLog m z) :=
  Nat.mul_pos (Nat.factorial_pos m) (pow_pos hz _)

theorem polynomial_embed (isLog : Bool) (m : ℕ) (z : Raw) :
    embed (interpret (polynomial isLog m z)) =
      ∑ k ∈ range m,
        (((z.1 : ℂ) + (z.2.1 : ℂ) * Complex.I) ^ k * (z.2.2 : ℂ) ^ (m - k) *
          (weight isLog m k : ℂ)) / ((m.factorial : ℂ) * (z.2.2 : ℂ) ^ m) := by
  rw [embed_interpret]
  simp only [polynomial, numerator, denominator, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow]
  rw [sum_mul, ← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro k _hk
  congr 1
  calc
    _ = ((component false k z.1 z.2.1 : ℂ) +
        (component true k z.1 z.2.1 : ℂ) * Complex.I) *
        (z.2.2 : ℂ) ^ (m - k) * (weight isLog m k : ℂ) := by ring
    _ = _ := by rw [power_embed]

theorem exp_correct (m : ℕ) {z : Raw} (hz : Valid z) :
    embed (interpret (polynomial false m z)) = embed (expTaylor m (interpret z)) := by
  rw [polynomial_embed, embed_expTaylor]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := (mem_range.mp hk).le
  have hD : (z.2.2 : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hz
  have hF : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hK : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hw : (weight false m k : ℂ) = (m.factorial : ℂ) / k.factorial := by
    simp only [weight, Bool.false_eq_true, if_false, Int.cast_natCast]
    exact Nat.cast_div (Nat.factorial_dvd_factorial hkm) hK
  have hpow : (z.2.2 : ℂ) ^ m = (z.2.2 : ℂ) ^ k * (z.2.2 : ℂ) ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkm]
  rw [hw, embed_interpret, div_pow, hpow]
  field_simp

theorem log_correct (m : ℕ) {z : Raw} (hz : Valid z) :
    embed (interpret (polynomial true m z)) = embed (logTaylor m (interpret z)) := by
  rw [polynomial_embed, embed_logTaylor, Complex.logTaylor]
  apply sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [weight]
  have hkm : k ≤ m := (mem_range.mp hk).le
  have hD : (z.2.2 : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hz
  have hF : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hK : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hw : (weight true m k : ℂ) =
      (-1 : ℂ) ^ (k + 1) * ((m.factorial : ℂ) / k) := by
    simp only [weight, if_true, if_neg hk0, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [Nat.cast_div (Nat.dvd_factorial (Nat.pos_of_ne_zero hk0) hkm) hK]
  have hpow : (z.2.2 : ℂ) ^ m = (z.2.2 : ℂ) ^ k * (z.2.2 : ℂ) ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkm]
  rw [hw, embed_interpret, div_pow, hpow]
  field_simp

theorem sum_range_polyT {α : Type} [Enc α] {n : α → ℕ} {f : α → ℕ → ℤ}
    (hn : Unary n) (hf : PolyT (fun p : α × ℕ => f p.1 (min p.2 (n p.1)))) :
    PolyT (fun x => ∑ k ∈ range (n x), f x k) :=
  (sumZ_polyT (map_range_polyT (f := f) hn hf)).congr (fun x => list_sum_range _ _)

theorem weight_polyT {α : Type} [Enc α] (isLog : Bool) {m k : α → ℕ}
    (hm : Unary m) (hk : Unary k) : PolyT (fun x => weight isLog (m x) (k x)) := by
  have hfacM := factorial_polyT hm
  have hfacK := factorial_polyT hk
  have hsgn : PolyT (fun x => (-1 : ℤ) ^ (k x + 1)) :=
    powZ_polyT (PolyT.const (-1)) (hk.add (Unary.const 1))
  have hkpoly := hk.poly
  unfold weight
  cases isLog <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

theorem numerator_polyT {α : Type} [Enc α] (isLog imag : Bool)
    {m : α → ℕ} {z : α → Raw} (hm : Unary m) (hz : PolyT z) :
    PolyT (fun x => numerator isLog imag (m x) (z x)) := by
  have hM : Unary (fun p : α × ℕ => m p.1) := hm.comp PolyT.id'.fst
  have hK : Unary (fun p : α × ℕ => min p.2 (m p.1)) :=
    unary_min_right PolyT.id'.snd hM
  have hZ : PolyT (fun p : α × ℕ => z p.1) := hz.comp PolyT.id'.fst
  have hA : PolyT (fun p : α × ℕ => (z p.1).1) := hZ.fst
  have hB : PolyT (fun p : α × ℕ => (z p.1).2.1) := hZ.snd.fst
  have hD : PolyT (fun p : α × ℕ => ((z p.1).2.2 : ℤ)) := PolyT.natCast hZ.snd.snd
  have hc := component_polyT imag hK hA hB
  have hp := powZ_polyT hD (unary_sub hM hK.poly)
  have hw := weight_polyT isLog hM hK
  apply sum_range_polyT (f := fun x k =>
    component imag k (z x).1 (z x).2.1 * ((z x).2.2 : ℤ) ^ (m x - k) * weight isLog (m x) k) hm
  exact PolyT.mulZ (PolyT.mulZ hc hp) hw

theorem denominator_polyT {α : Type} [Enc α] {m : α → ℕ} {z : α → Raw}
    (hm : Unary m) (hz : PolyT z) : PolyT (fun x => denominator (m x) (z x)) :=
  PolyT.mul (factorial_polyT hm) (PolyT.pow_unary hz.snd.snd hm)

theorem polynomial_polyT {α : Type} [Enc α] (isLog : Bool)
    {m : α → ℕ} {z : α → Raw} (hm : Unary m) (hz : PolyT z) :
    PolyT (fun x => polynomial isLog (m x) (z x)) :=
  PolyT.prodMk (numerator_polyT isLog false hm hz)
    (PolyT.prodMk (numerator_polyT isLog true hm hz) (denominator_polyT hm hz))

end PrimeAlgorithm.CertifiedRawTaylor
