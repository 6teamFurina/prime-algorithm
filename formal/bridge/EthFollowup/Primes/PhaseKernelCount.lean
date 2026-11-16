import EthFollowup.Primes.PhaseKernelDesc

set_option maxHeartbeats 2000000

namespace EthFollowup.Primes.PhaseKernel

open Finset EthFollowup.ModP

def horizontal (neg : Bool) (U Q d t : ℕ) : ℕ :=
  if neg then Q*t-U*d else U*d-Q*t

def denominator (neg : Bool) (U V Q d t : ℕ) : ℕ :=
  horizontal neg U Q d t * horizontal neg U Q d t + (V*d)*(V*d)

def numerator (neg imag : Bool) (U V Q d t S : ℕ) : ℕ :=
  S*((Q*d)*(if imag then V*d else horizontal neg U Q d t))

def quotient (neg imag : Bool) (U V Q d t S : ℕ) : ℕ :=
  numerator neg imag U V Q d t S / denominator neg U V Q d t

/-- The unique auxiliary assignment, with only the weight witness left free. -/
def canonical (neg imag : Bool) (U V Q d t S w : ℕ) (j : Fin 15) : ℕ :=
  match j.val with
  | 0 => U
  | 1 => V
  | 2 => Q
  | 3 => d
  | 4 => t
  | 5 => S
  | 6 => horizontal neg U Q d t
  | 7 => V*d
  | 8 => denominator neg U V Q d t
  | 9 => Q*d
  | 10 => (Q*d)*(if imag then V*d else horizontal neg U Q d t)
  | 11 => numerator neg imag U V Q d t S
  | 12 => quotient neg imag U V Q d t S
  | 13 => numerator neg imag U V Q d t S % denominator neg U V Q d t
  | _ => w

def InputRelations (neg imag : Bool) (U V Q d t S : ℕ) (x : Fin 15 → ℕ) : Prop :=
  x 0=U ∧ x 1=V ∧ x 2=Q ∧ x 3=d ∧ x 4=t ∧ x 5=S ∧
    Relations neg imag (extV 15 x)

private theorem quotient_unique {A D q r : ℕ}
    (hr : r<D) (he : A=D*q+r) : q=A/D ∧ r=A%D := by
  have hq : A/D=q := Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  refine ⟨hq.symm, ?_⟩
  have := Nat.div_add_mod A D
  nlinarith

theorem inputRelations_unique {neg imag : Bool} {U V Q d t S : ℕ}
    (x : Fin 15 → ℕ) (hx : InputRelations neg imag U V Q d t S x) :
    x = canonical neg imag U V Q d t S (x 14) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,hr⟩ := hx
  simp only [Relations, extV] at hr
  simp only [show (0:ℕ)<15 by decide, show (1:ℕ)<15 by decide,
    show (2:ℕ)<15 by decide, show (3:ℕ)<15 by decide,
    show (4:ℕ)<15 by decide, show (5:ℕ)<15 by decide,
    show (6:ℕ)<15 by decide, show (7:ℕ)<15 by decide,
    show (8:ℕ)<15 by decide, show (9:ℕ)<15 by decide,
    show (10:ℕ)<15 by decide, show (11:ℕ)<15 by decide,
    show (12:ℕ)<15 by decide, show (13:ℕ)<15 by decide,
    show (14:ℕ)<15 by decide, dite_true] at hr
  obtain ⟨h6,h7,h8,h9,h10,h11,hdiv,hpos,hrem,hw⟩ := hr
  have ha : x 6 = horizontal neg U Q d t := by
    cases neg <;> simp [horizontal,h0,h2,h3,h4] at h6 ⊢ <;> omega
  have hb : x 7=V*d := by simpa [h1,h3] using h7
  have hD : x 8=denominator neg U V Q d t := by simpa [denominator,ha,hb] using h8
  have hQd : x 9=Q*d := by simpa [h2,h3] using h9
  have h10' : x 10=(Q*d)*(if imag then V*d else horizontal neg U Q d t) := by
    change x 10=x 9*(if imag then x 7 else x 6) at h10
    rw [hQd,ha,hb] at h10
    exact h10
  have hnum : x 11=numerator neg imag U V Q d t S := by
    change x 11=S*((Q*d)*(if imag then V*d else horizontal neg U Q d t))
    rw [←h10',←h5]
    exact h11
  have hqr := quotient_unique (by simpa [hD] using hrem)
    (by simpa [hnum,hD] using hdiv)
  have hq : x 12=quotient neg imag U V Q d t S := hqr.1
  have hrem' : x 13=numerator neg imag U V Q d t S % denominator neg U V Q d t := hqr.2
  funext j
  fin_cases j <;> simp [canonical,h0,h1,h2,h3,h4,h5,ha,hb,hD,hQd,h10',hnum,hq,hrem']

theorem canonical_relations {neg imag : Bool} {U V Q d t S w : ℕ}
    (hsign : if neg then U*d<Q*t else Q*t≤U*d)
    (hD : 0<denominator neg U V Q d t)
    (hw : w<quotient neg imag U V Q d t S) :
    InputRelations neg imag U V Q d t S (canonical neg imag U V Q d t S w) := by
  have ha : (if neg then U*d+horizontal neg U Q d t=Q*t ∧
      1≤horizontal neg U Q d t else U*d=Q*t+horizontal neg U Q d t) := by
    cases neg <;> simp [horizontal] at hsign ⊢ <;> omega
  have hr := Nat.mod_lt (numerator neg imag U V Q d t S) hD
  have hdiv := (Nat.div_add_mod (numerator neg imag U V Q d t S)
    (denominator neg U V Q d t)).symm
  simpa [InputRelations,Relations,extV,canonical,denominator,numerator,quotient,
    Nat.mul_comm] using And.intro ha (And.intro hdiv
      (And.intro (by omega : 1≤denominator neg U V Q d t) (And.intro hr hw)))

def solutions (neg imag : Bool) (b l U V Q d t S box : ℕ) : Finset (Fin 15 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 15 => range box).filter
    fun x => (pinnedDesc neg imag b l U V Q d t S).D.Sat b (extV 15 x)

theorem mem_solutions {neg imag : Bool} {b l U V Q d t S box : ℕ}
    (hU : U<2^(b*l)) (hV : V<2^(b*l)) (hQ : Q<2^(b*l))
    (hd : d<2^(b*l)) (ht : t<2^(b*l)) (hS : S<2^(b*l)) (x : Fin 15 → ℕ) :
    x ∈ solutions neg imag b l U V Q d t S box ↔
      (∀j, x j<box) ∧ InputRelations neg imag U V Q d t S x := by
  simp [solutions,pinnedDesc_sat hU hV hQ hd ht hS,InputRelations,extV]

theorem inputRelations_weight {neg imag : Bool} {U V Q d t S : ℕ}
    (x : Fin 15 → ℕ) (hx : InputRelations neg imag U V Q d t S x) :
    x 14<quotient neg imag U V Q d t S := by
  have he := inputRelations_unique x hx
  obtain ⟨_,_,_,_,_,_,hr⟩ := hx
  obtain ⟨_,_,_,_,_,_,_,_,_,hw⟩ := hr
  change x 14<x 12 at hw
  have hq : x 12=quotient neg imag U V Q d t S := congrArg (fun f => f 12) he
  exact hq ▸ hw

/-- Every satisfying assignment is uniquely indexed by a weight witness below
the exact floor quotient.  The box hypothesis only excludes truncation. -/
theorem pinnedDesc_count {neg imag : Bool} {b l U V Q d t S : ℕ} (bx : ℕ → ℕ)
    (hU : U<2^(b*l)) (hV : V<2^(b*l)) (hQ : Q<2^(b*l))
    (hd : d<2^(b*l)) (ht : t<2^(b*l)) (hS : S<2^(b*l))
    (hsign : if neg then U*d<Q*t else Q*t≤U*d)
    (hD : 0<denominator neg U V Q d t)
    (hbox : ∀w<quotient neg imag U V Q d t S,
      ∀j, canonical neg imag U V Q d t S w j<bx 0) :
    (pinnedDesc neg imag b l U V Q d t S).countB b bx =
      quotient neg imag U V Q d t S := by
  change (solutions neg imag b l U V Q d t S (bx 0)).card = _
  rw [←card_range (quotient neg imag U V Q d t S)]
  apply card_nbij (fun x : Fin 15 → ℕ => x 14)
  · intro x hx
    have hr := ((mem_solutions hU hV hQ hd ht hS x).mp hx).2
    exact mem_range.mpr (inputRelations_weight x hr)
  · intro x hx y hy he
    change x 14=y 14 at he
    have hx' := ((mem_solutions hU hV hQ hd ht hS x).mp hx).2
    have hy' := ((mem_solutions hU hV hQ hd ht hS y).mp hy).2
    calc x = canonical neg imag U V Q d t S (x 14) := inputRelations_unique x hx'
      _ = canonical neg imag U V Q d t S (y 14) := by rw [he]
      _ = y := (inputRelations_unique y hy').symm
  · intro w hw
    have hw' := mem_range.mp hw
    refine ⟨canonical neg imag U V Q d t S w, ?_, rfl⟩
    exact (mem_solutions hU hV hQ hd ht hS _).mpr
      ⟨hbox w hw', canonical_relations hsign hD hw'⟩

open EthFollowup.Factoring EthFollowup.ExactHC

/-- Exact value of the constructed arithmetic network for this Cauchy kernel. -/
theorem actualNetwork_value (neg imag : Bool) {n g U V Q d t S : ℕ} (hg : 2≤g)
    (hU : U<lbox n 0) (hV : V<lbox n 0) (hQ : Q<lbox n 0)
    (hd : d<lbox n 0) (ht : t<lbox n 0) (hS : S<lbox n 0)
    (hsign : if neg then U*d<Q*t else Q*t≤U*d)
    (hD : 0<denominator neg U V Q d t)
    (hbox : ∀w<quotient neg imag U V Q d t S,
      ∀j, canonical neg imag U V Q d t S w j<lbox n 0) :
    ((arithSys n (actualDesc neg imag n U V Q d t S) g hg).net (aLabCode n)).value =
      (quotient neg imag U V Q d t S : ℕ) := by
  rw [arithNet_value hg (actualDesc_WF neg imag n U V Q d t S)]
  congr 1
  exact pinnedDesc_count (lbox n) hU hV hQ hd ht hS hsign hD hbox

end EthFollowup.Primes.PhaseKernel
