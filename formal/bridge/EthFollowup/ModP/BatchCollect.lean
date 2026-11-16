import EthFollowup.ModP.BatchNatQueries

set_option maxHeartbeats 1000000

namespace EthFollowup.ModP.BatchCollect
open Groundwork EthFollowup.ExactHC EthFollowup.Factoring

abbrev Item := List Bool × ℤ

def spec (items : List Bool → List Item)
    (finish : List Bool × List ℕ → List Bool) : NatBatchQuerySpec where
  rounds w := (items w).length
  initial _ := []
  query p := ((items p.1).getD p.2.1 ([],0)).1
  update p := p.1.2.2 ++ [p.2.toNat]
  finish := finish

variable {items : List Bool → List Item} {finish : List Bool × List ℕ → List Bool}

theorem rounds_polyT (hitems : PolyT items) : PolyT (spec items finish).rounds := by
  change PolyT fun w => (items w).length
  fun_prop

theorem initial_polyT : PolyT (spec items finish).initial := PolyT.const []

theorem query_polyT (hitems : PolyT items) : PolyT (spec items finish).query := by
  change PolyT fun p : NatBatchIn => ((items p.1).getD p.2.1 ([],0)).1
  fun_prop

theorem update_polyT : PolyT (spec items finish).update := by
  change PolyT fun p : NatBatchIn × ℤ => p.1.2.2 ++ [p.2.toNat]
  fun_prop

variable {c₀ : ℕ} (pk : CntPackage c₀)

def counts (w : List Bool) (i : ℕ) : List ℕ :=
  (List.range i).map fun j => pk.Q w (((items w).getD j ([],0)).1)

theorem seq_eq (w : List Bool) (i : ℕ) :
    NatBatchQuery.seq pk (spec items finish) w i = counts pk (items:=items) w i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change NatBatchQuery.seq pk (spec items finish) w i ++
      [pk.Q w (((items w).getD i ([],0)).1)] = _
    rw [ih]
    simp only [counts,List.range_succ,List.map_append,
      List.map_cons,List.map_nil,Int.toNat_natCast]

theorem answer_eq (w : List Bool) :
    NatBatchQuery.answer pk (spec items finish) w =
      finish (w,(items w).map fun q => pk.Q w q.1) := by
  unfold NatBatchQuery.answer
  rw [seq_eq]
  change finish (w,(List.range (items w).length).map
    (fun j=>pk.Q w (((items w).getD j ([],0)).1)))=_
  congr 2
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.length_map,List.length_range] at hj
    simp [List.getD_eq_getElem (items w) ([],0) hj,hj]

theorem size_list_append (l r : List ℕ) : size (l++r)+1=size l+size r := by
  simp only [size_list,List.map_append,List.sum_append]
  omega

theorem counts_size {w : List Bool} {i : ℕ}
    (hv : ∀j < i,pk.Ok w ∧ (((items w).getD j ([],0)).1).length≤pk.R w) :
    size (counts pk (items:=items) w i) ≤ i * (pk.qb*(w.length+2)+2)+1 := by
  induction i with
  | zero => simp [counts,size_list]
  | succ i ih =>
    have hi := ih (fun j hj=>hv j (by omega))
    obtain ⟨hok,hq⟩ := hv i (by omega)
    have hs := GR.size_Q_le pk hok hq
    simp only [size_int,Int.natAbs_natCast] at hs
    have he : counts pk (items:=items) w (i+1)=
        counts pk (items:=items) w i++[pk.Q w (((items w).getD i ([],0)).1)] := by
      simp [counts,List.range_succ]
    rw [he]
    have ha := size_list_append (counts pk (items:=items) w i)
      [pk.Q w (((items w).getD i ([],0)).1)]
    have hs' : size [pk.Q w (((items w).getD i ([],0)).1)] ≤ pk.qb*(w.length+2)+3 := by
      simp only [size_list,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,size_nat]
      omega
    rw [Nat.succ_mul]
    omega

/-- A polynomially generated list of valid queries may be collected in full.
The list of counts has polynomial size because each count has linear bit size. -/
theorem bounds (hitems : PolyT items) (hf : PolyT finish)
    (hvalid : ∀w i,i<(items w).length →
      pk.Ok w ∧ (((items w).getD i ([],0)).1).length≤pk.R w) :
    ∃a,NatBatchQuery.Bounds pk (spec items finish) a := by
  obtain ⟨r,hr,_,hrlen⟩ := hitems.len_bound
  obtain ⟨o,ho,hmono,holen⟩ := hf.len_bound
  let R : ℕ→ℕ := fun n=>r (3*n+2)
  have hR : PB R := hr.comp (((PB.const 3).mul PB.id').add (PB.const 2))
  have hround (w : List Bool) : (items w).length≤R w.length := by
    exact (length_le_len _).trans (by simpa only [len_bools] using hrlen w)
  let S : ℕ→ℕ := fun n=>R n*(pk.qb*(n+2)+2)+1
  have hS : PB S :=
    (hR.mul (((PB.const pk.qb).mul (PB.id'.add (PB.const 2))).add (PB.const 2))).add (PB.const 1)
  have hstate (w : List Bool) (i : ℕ) (hi : i≤(items w).length) :
      size (NatBatchQuery.seq pk (spec items finish) w i)≤S w.length := by
    rw [seq_eq]
    exact (counts_size pk (fun j hj=>hvalid w j (by omega))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hi.trans (hround w))) _)
  let O : ℕ→ℕ := fun n=>2*o (7*(2*n+1+S n))+1
  have hO : PB O := (PB.const 2).mul
    (ho.comp ((PB.const 7).mul ((((PB.const 2).mul PB.id').add (PB.const 1)).add hS))) |>.add (PB.const 1)
  have hout (w : List Bool) : size (NatBatchQuery.answer pk (spec items finish) w)≤O w.length := by
    let s := NatBatchQuery.seq pk (spec items finish) w (items w).length
    have hs : size s≤S w.length := hstate w _ le_rfl
    have hh := holen (w,s)
    have hc := Carried.le (w,s)
    have hinput : len (w,s)≤7*(2*w.length+1+S w.length) := by
      simp only [size_prod,FR.size_bools] at hc
      omega
    have he : len (finish (w,s))≤o (7*(2*w.length+1+S w.length)) :=
      hh.trans (hmono hinput)
    change size (finish (w,s))≤_
    simp only [FR.size_bools,len_bools] at he ⊢
    dsimp [O]
    omega
  obtain ⟨a,ha⟩ := (hR.add hS).add hO
  have hbound (n : ℕ) : R n+S n+O n≤a*(n+2)^a :=
    (ha n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  refine ⟨a,⟨?_,?_,?_,?_⟩⟩
  · intro w
    have := hround w
    have := hbound w.length
    change (items w).length≤_
    omega
  · intro w i hi
    have := hstate w i hi
    have := hbound w.length
    omega
  · intro w
    have := hout w
    have := hbound w.length
    omega
  · intro w i hi
    exact hvalid w i hi

end EthFollowup.ModP.BatchCollect
