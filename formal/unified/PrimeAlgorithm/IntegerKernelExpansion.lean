import PrimeAlgorithm.IntegerPrimeSum
import PrimeAlgorithm.KernelSumExpansion
import EthFollowup.Primes.FourKernelCountFinal

set_option maxHeartbeats 3000000

namespace PrimeAlgorithm.IntegerKernelExpansion
open Finset CertifiedCauchy CertifiedNumerator

def gaussian (z : GaussianIntPair) : GaussianInt := ⟨z.1,z.2⟩

def gaussianAdd : GaussianIntPair →+ GaussianInt where
  toFun := gaussian
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem gaussian_zero : gaussian (0:GaussianIntPair)=0 := rfl
@[simp] theorem gaussian_add (z w : GaussianIntPair) :
    gaussian (z+w)=gaussian z+gaussian w := rfl
@[simp] theorem gaussian_neg (z : GaussianIntPair) : gaussian (-z) = -gaussian z := rfl
theorem gaussian_sum {α : Type*} (s : Finset α) (f : α → GaussianIntPair) :
    gaussian (∑i∈s,f i)=∑i∈s,gaussian (f i) := map_sum gaussianAdd f s
theorem gaussian_nsmul (n : ℕ) (z : GaussianIntPair) :
    gaussian (n • z)=(n:GaussianInt)*gaussian z := by
  change gaussianAdd (n • z)=_
  rw [map_nsmul,nsmul_eq_mul]
  rfl

@[simp] theorem gaussian_multiply (z w : GaussianIntPair) :
    gaussian (multiply z w)=gaussian z*gaussian w := by
  apply Zsqrtd.ext <;> simp [gaussian,multiply,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

def horizontalSign (p : ℕ) (z : GaussianIntPair) (num den : ℕ) : Bool :=
  decide (z.1.toNat*den<2^p*num)

def componentSign (z : GaussianIntPair) (imag neg : Bool) : GaussianInt :=
  if imag then ⟨0,if z.2<0 then 1 else -1⟩ else if neg then -1 else 1

def componentQuotient (p t : ℕ) (z : GaussianIntPair) (num den : ℕ) (imag : Bool) : ℕ :=
  EthFollowup.Primes.PhaseKernel.quotient (horizontalSign p z num den) imag z.1.toNat z.2.natAbs (2^p) den num (2^t)

theorem horizontal_natAbs (p : ℕ) (z : GaussianIntPair) (num den : ℕ) (hz : 0≤z.1) :
    (horizontal p z num den).natAbs =
      EthFollowup.Primes.PhaseKernel.horizontal (horizontalSign p z num den) z.1.toNat (2^p) den num := by
  have he : horizontal p z num den=(z.1.toNat*den:ℕ)-(2^p*num:ℕ) := by
    simp [horizontal,Int.toNat_of_nonneg hz]
  rw [he]
  unfold horizontalSign EthFollowup.Primes.PhaseKernel.horizontal
  by_cases h : z.1.toNat*den<2^p*num
  · simp only [h,decide_true,Bool.coe_true,ite_true]
    exact Int.natAbs_natCast_sub_natCast_of_le h.le
  · simp only [h,decide_false,Bool.false_eq_true,ite_false]
    exact Int.natAbs_natCast_sub_natCast_of_ge (by omega)

theorem denominator_eq (p : ℕ) (z : GaussianIntPair) (num den : ℕ) (hz : 0≤z.1) :
    denominator p z num den = EthFollowup.Primes.PhaseKernel.denominator (horizontalSign p z num den)
      z.1.toNat z.2.natAbs (2^p) den num := by
  simp only [denominator,horizontal_natAbs p z num den hz,vertical,Int.natAbs_mul,
    Int.natAbs_natCast,EthFollowup.Primes.PhaseKernel.denominator,pow_two]

theorem signedQuotient_nat_mul (t k : ℕ) (a : ℤ) (D : ℕ) :
    signedQuotient t ((k:ℤ)*a) D =
      (if a<0 then (-1:ℤ) else 1)*((2^t*(k*a.natAbs)/D:ℕ):ℤ) := by
  by_cases hk : k=0
  · subst k; simp [signedQuotient]
  · have hk' : (0:ℤ)<k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
    have hh : (k:ℤ)*a<0 ↔ a<0 := by constructor <;> intro h <;> nlinarith
    simp only [signedQuotient,hh,Int.natAbs_mul,Int.natAbs_natCast]
    split <;> simp

theorem reciprocal_expansion (p t : ℕ) (z : GaussianIntPair) (num den : ℕ)
    (hz : 0≤z.1) :
    gaussian (reciprocalNumerator p t z num den) =
      ∑imag:Bool,componentSign z imag (horizontalSign p z num den)*
        (componentQuotient p t z num den imag:GaussianInt) := by
  have hneg : horizontal p z num den<0 ↔ z.1.toNat*den<2^p*num := by
    have he : horizontal p z num den=(z.1.toNat*den:ℕ)-(2^p*num:ℕ) := by
      simp [horizontal,Int.toNat_of_nonneg hz]
    rw [he,sub_neg]
    exact Int.ofNat_lt
  have hr := signedQuotient_nat_mul t (2^p*den) (horizontal p z num den)
    (denominator p z num den)
  have hi := signedQuotient_nat_mul t (2^p*den*den) (-z.2)
    (denominator p z num den)
  have hi' : -((2^p:ℤ)*den*vertical z den)=(2^p*den*den:ℕ)*(-z.2) := by
    simp only [vertical,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    ring
  have hr' : ((2^p:ℤ)*den*horizontal p z num den)=
      (2^p*den:ℕ)*horizontal p z num den := by simp
  simp only [reciprocalNumerator,hr',hi',hr,hi]
  rw [horizontal_natAbs p z num den hz,denominator_eq p z num den hz] at hr
  simp only [Int.natAbs_neg] at hi
  apply Zsqrtd.ext
  · simp only [gaussian,componentSign,Fintype.sum_bool,componentQuotient,
      Bool.false_eq_true,ite_false,Bool.coe_true,ite_true,
      Zsqrtd.re_add,Zsqrtd.re_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast,
      Zsqrtd.re_natCast,Zsqrtd.im_natCast,mul_zero,mul_one,zero_mul,add_zero]
    simp only [horizontalSign,Bool.decide_coe,hneg,EthFollowup.Primes.PhaseKernel.quotient,EthFollowup.Primes.PhaseKernel.numerator,
      Bool.false_eq_true,ite_false,denominator_eq p z num den hz,
      horizontal_natAbs p z num den hz]
    by_cases hh : z.1.toNat*den<2^p*num <;> simp only [hh,decide_true,decide_false,ite_true,ite_false,Zsqrtd.re_neg,Zsqrtd.re_one,neg_mul,one_mul,zero_add,Bool.false_eq_true]
  · simp only [gaussian,componentSign,Fintype.sum_bool,componentQuotient,
      Bool.false_eq_true,ite_false,Bool.coe_true,ite_true,
      Zsqrtd.im_add,Zsqrtd.im_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast,
      Zsqrtd.re_natCast,Zsqrtd.im_natCast,mul_zero,mul_one,zero_mul,zero_add,add_zero]
    simp only [EthFollowup.Primes.PhaseKernel.quotient,EthFollowup.Primes.PhaseKernel.numerator,Bool.coe_true,ite_true,
      denominator_eq p z num den hz,Int.natAbs_neg]
    have hre : (if horizontalSign p z num den then (-1:GaussianInt) else 1).im=0 := by
      cases horizontalSign p z num den <;> simp
    rw [hre,zero_mul,add_zero]
    have he : 2^t*(2^p*den*den*z.2.natAbs)=2^t*(2^p*den*(z.2.natAbs*den)) := by ring
    rw [he]
    by_cases hz0 : z.2=0
    · simp [hz0]
    · by_cases hzneg : z.2<0
      · simp [hzneg,show ¬(0<z.2) by omega]
      · simp [hzneg,show 0<z.2 by omega]

theorem numerator_expansion (p t M : ℕ) (D : Data) (num den : ℕ)
    (hz : ∀j<M,0≤(D.pole j).1) :
    gaussian (numerator p t M D num den) =
      ∑j:Fin M × Bool,gaussian (D.residue j.1)*
        componentSign (D.pole j.1) j.2 (horizontalSign p (D.pole j.1) num den)*
        (componentQuotient p t (D.pole j.1) num den j.2:GaussianInt) := by
  unfold numerator
  rw [gaussian_sum]
  simp_rw [gaussian_multiply]
  rw [←Fin.sum_univ_eq_sum_range]
  simp_rw [reciprocal_expansion p t _ num den (hz _ (Fin.isLt _)),mul_sum]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

end PrimeAlgorithm.IntegerKernelExpansion
