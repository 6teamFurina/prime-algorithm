import PrimeAlgorithm.CertifiedGaussianRat
import ToTuring.Lib.Int

set_option maxHeartbeats 1000000

/-! Gaussian rationals represented by two signed numerators and one positive
common denominator. No operation invokes rational normalization or gcd. -/

namespace PrimeAlgorithm.CertifiedRawGaussian

open CertifiedGaussianRat

abbrev Raw := ℤ × ℤ × ℕ

def Valid (z : Raw) : Prop := 0 < z.2.2

def interpret (z : Raw) : QComplex := ⟨(z.1 : ℚ) / z.2.2, (z.2.1 : ℚ) / z.2.2⟩

theorem embed_interpret (z : Raw) :
    embed (interpret z) = ((z.1 : ℂ) + (z.2.1 : ℂ) * Complex.I) / z.2.2 := by
  rw [embed_apply]
  simp only [interpret, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  ring

def zero : Raw := (0, 0, 1)
def one : Raw := (1, 0, 1)
def ofInt (n : ℤ) : Raw := (n, 0, 1)
def neg (z : Raw) : Raw := (-z.1, -z.2.1, z.2.2)
def add (z w : Raw) : Raw :=
  (z.1 * w.2.2 + w.1 * z.2.2, z.2.1 * w.2.2 + w.2.1 * z.2.2, z.2.2 * w.2.2)
def mul (z w : Raw) : Raw :=
  (z.1 * w.1 - z.2.1 * w.2.1, z.1 * w.2.1 + z.2.1 * w.1, z.2.2 * w.2.2)
def inv (z : Raw) : Raw :=
  if z.1 = 0 ∧ z.2.1 = 0 then zero else
    (z.1 * z.2.2, -(z.2.1 * z.2.2), z.1.natAbs ^ 2 + z.2.1.natAbs ^ 2)
def div (z w : Raw) : Raw := mul z (inv w)

theorem valid_zero : Valid zero := by norm_num [Valid, zero]
theorem valid_one : Valid one := by norm_num [Valid, one]
theorem valid_ofInt (n : ℤ) : Valid (ofInt n) := by norm_num [Valid, ofInt]
theorem valid_neg {z : Raw} (hz : Valid z) : Valid (neg z) := hz
theorem valid_add {z w : Raw} (hz : Valid z) (hw : Valid w) : Valid (add z w) :=
  Nat.mul_pos hz hw
theorem valid_mul {z w : Raw} (hz : Valid z) (hw : Valid w) : Valid (mul z w) :=
  Nat.mul_pos hz hw
theorem valid_inv (z : Raw) : Valid (inv z) := by
  unfold inv
  split_ifs with h
  · exact valid_zero
  · dsimp [Valid]
    have hsum : z.1.natAbs ≠ 0 ∨ z.2.1.natAbs ≠ 0 := by
      simpa using not_and_or.mp h
    rcases hsum with h₁ | h₂
    · have : 0 < z.1.natAbs ^ 2 := pow_pos (Nat.pos_of_ne_zero h₁) _
      omega
    · have : 0 < z.2.1.natAbs ^ 2 := pow_pos (Nat.pos_of_ne_zero h₂) _
      omega
theorem valid_div {z : Raw} (hz : Valid z) (w : Raw) : Valid (div z w) :=
  valid_mul hz (valid_inv w)

@[simp] theorem interpret_zero : interpret zero = 0 := by
  ext <;> simp [interpret, zero]
@[simp] theorem interpret_one : interpret one = 1 := by
  ext <;> simp [interpret, one, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
@[simp] theorem interpret_ofInt (n : ℤ) : interpret (ofInt n) = n := by
  ext <;> simp [interpret, ofInt]
@[simp] theorem interpret_neg (z : Raw) : interpret (neg z) = -interpret z := by
  ext <;> simp [interpret, neg, neg_div]

theorem interpret_add {z w : Raw} (hz : Valid z) (hw : Valid w) :
    interpret (add z w) = interpret z + interpret w := by
  have hz0 : (z.2.2 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hz
  have hw0 : (w.2.2 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  ext <;> simp only [interpret, add, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  all_goals push_cast <;> field_simp <;> ring

theorem interpret_mul {z w : Raw} (hz : Valid z) (hw : Valid w) :
    interpret (mul z w) = interpret z * interpret w := by
  have hz0 : (z.2.2 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hz
  have hw0 : (w.2.2 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  ext <;> simp only [interpret, mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  all_goals push_cast <;> field_simp <;> ring

theorem interpret_inv {z : Raw} (hz : Valid z) : interpret (inv z) = (interpret z)⁻¹ := by
  by_cases h : z.1 = 0 ∧ z.2.1 = 0
  · have he : interpret z = 0 := by ext <;> simp [interpret, h.1, h.2]
    simp [inv, h, he]
  · have hd : (z.2.2 : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hz
    have hsN : 0 < z.1.natAbs ^ 2 + z.2.1.natAbs ^ 2 := by
      simpa only [inv, if_neg h, Valid] using valid_inv z
    have hs : ((z.1.natAbs ^ 2 + z.2.1.natAbs ^ 2 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hsN
    have hsq : ((z.1.natAbs ^ 2 + z.2.1.natAbs ^ 2 : ℕ) : ℚ) =
        (z.1 : ℚ) ^ 2 + (z.2.1 : ℚ) ^ 2 := by
      push_cast
      simp [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    have hs' : (z.1 : ℚ) ^ 2 + (z.2.1 : ℚ) ^ 2 ≠ 0 := hsq ▸ hs
    apply eq_inv_of_mul_eq_one_left
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      interpret, inv, if_neg h, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    all_goals push_cast <;> simp only [Nat.cast_natAbs, Int.cast_abs, sq_abs] <;>
      field_simp <;> ring

theorem interpret_div {z w : Raw} (hz : Valid z) (hw : Valid w) :
    interpret (div z w) = interpret z / interpret w := by
  rw [div, interpret_mul hz (valid_inv w), interpret_inv hw, div_eq_mul_inv]

open Groundwork

theorem add_polyT : PolyT (fun zw : Raw × Raw => add zw.1 zw.2) := by
  unfold add
  fun_prop

theorem mul_polyT : PolyT (fun zw : Raw × Raw => mul zw.1 zw.2) := by
  unfold mul
  fun_prop

theorem neg_polyT : PolyT neg := by
  unfold neg
  fun_prop

theorem inv_polyT : PolyT inv := by
  unfold inv zero
  fun_prop

theorem div_polyT : PolyT (fun zw : Raw × Raw => div zw.1 zw.2) := by
  unfold div mul inv zero
  fun_prop

@[fun_prop] theorem add_apply_polyT {α : Type} [Enc α] {f g : α → Raw}
    (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => add (f x) (g x)) := by
  exact PolyT.prodMk
    (PolyT.addZ (PolyT.mulZ hf.fst (PolyT.natCast hg.snd.snd))
      (PolyT.mulZ hg.fst (PolyT.natCast hf.snd.snd)))
    (PolyT.prodMk
      (PolyT.addZ (PolyT.mulZ hf.snd.fst (PolyT.natCast hg.snd.snd))
        (PolyT.mulZ hg.snd.fst (PolyT.natCast hf.snd.snd)))
      (PolyT.mul hf.snd.snd hg.snd.snd))

@[fun_prop] theorem mul_apply_polyT {α : Type} [Enc α] {f g : α → Raw}
    (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => mul (f x) (g x)) := by
  exact PolyT.prodMk
    (PolyT.subZ (PolyT.mulZ hf.fst hg.fst) (PolyT.mulZ hf.snd.fst hg.snd.fst))
    (PolyT.prodMk
      (PolyT.addZ (PolyT.mulZ hf.fst hg.snd.fst) (PolyT.mulZ hf.snd.fst hg.fst))
      (PolyT.mul hf.snd.snd hg.snd.snd))

@[fun_prop] theorem neg_apply_polyT {α : Type} [Enc α] {f : α → Raw}
    (hf : PolyT f) : PolyT (fun x => neg (f x)) := by
  exact PolyT.prodMk (PolyT.negZ hf.fst) (PolyT.prodMk (PolyT.negZ hf.snd.fst) hf.snd.snd)

@[fun_prop] theorem inv_apply_polyT {α : Type} [Enc α] {f : α → Raw}
    (hf : PolyT f) : PolyT (fun x => inv (f x)) := inv_polyT.comp hf

@[fun_prop] theorem div_apply_polyT {α : Type} [Enc α] {f g : α → Raw}
    (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => div (f x) (g x)) :=
  mul_apply_polyT hf (inv_apply_polyT hg)

end PrimeAlgorithm.CertifiedRawGaussian
