import PrimeAlgorithm.PrimeSumMachine

/-! The already constructed prime-sum algorithm as a composable stepped
machine, including coefficient generation, count queries and linear padding. -/

set_option maxHeartbeats 500000
noncomputable section
namespace PrimeAlgorithm.PrimeSumOracle
open Groundwork Groundwork.Prog EthFollowup.ModP EthFollowup.Primes
  EthFollowup.ExactHC Eight.SecNetworks Printed QueryMachines EthFollowup.Factoring
  PrimeMachineInput CertifiedGenerator PrimeSumMachine

theorem stepped_of_package {c₀ : ℕ} (pk : CntPackage c₀)
    (hR : ∀w,pk.R w=w.length) (hOk : ∀w,pk.Ok w)
    (hlen : ∀w q,q∈rawItems w → q.1.length≤(LinearPadding.pad w).length)
    (hsum : ∀w,((rawItems w).map fun q=>q.2*(pk.Q (LinearPadding.pad w) q.1:ℤ)).sum=
      (IntegerPrimeQueryFinal.queryNumerator (precision w) (ofWord w) (generate (precision w))).re) :
    ∃ Mc : Stepped (List Bool) (List Bool), Nonempty (IsPolyT Mc) ∧
      ∃ A : ℕ, ∀ w : List Bool, ∃ T S : ℕ,
        Mc.Runs w T S (Nat.bits (primeSum (ofWord w))) ∧
        (T:ℝ)≤(2:ℝ)^T2.Xp A w.length 0 ∧
        (S:ℝ)≤(2:ℝ)^T2.Xp A w.length 0 ∧
        (w.length:ℝ)≤(2:ℝ)^T2.Xp A w.length 0 := by
  obtain ⟨a,hb⟩ := bounds pk hR hOk
  have hf : PolyT spec.finish := by
    dsimp only [spec,BatchCollect.spec]
    exact finish_polyT
  obtain ⟨c,x₀,C₀,D',Alg,-,-,-,-,-,he,hyp,-⟩ := CountedRoute.onTheCountedRecursion
  obtain ⟨C₁,hC₁⟩ := T2.geBody
  obtain ⟨iM⟩ := NatBatchQuery.machine_poly pk spec _ hyp.levels hyp.computesK hyp.steps
    (BatchCollect.rounds_polyT (finish:=finish) items_polyT)
    (BatchCollect.initial_polyT (items:=items) (finish:=finish))
    (BatchCollect.query_polyT (finish:=finish) items_polyT)
    (BatchCollect.update_polyT (items:=items) (finish:=finish)) hf
  obtain ⟨A,hA⟩ := NatBatchQuery.machine_runs pk spec hb hC₁ hyp.levels hyp.computesK _
    hyp.solves (x₀:=x₀) (fun l=>he l)
  refine ⟨Stepped.mapIn LinearPadding.pad (NatBatchQuery.machine pk spec
    (ExplicitCost.cliqueMachine (c+2) x₀ Alg) (CliqueLevels.levelsUnder x₀)
    (_root_.Levels.Gen.K x₀ 0)),⟨IsPolyT.mapIn LinearPadding.pad_polyT⟩,
    A*2049,fun w=>?_⟩
  obtain ⟨T,S,hrun,hT,hS,hn⟩ := hA (LinearPadding.pad w)
  have hpow : (2:ℝ)^T2.Xp A (LinearPadding.pad w).length 0 ≤
      (2:ℝ)^T2.Xp (A*2049) w.length 0 :=
    Real.rpow_le_rpow_of_exponent_le one_le_two
      (NatBatchQuery.Xp_linear_input (LinearPadding.pad_length_bounds w).1
        (LinearPadding.pad_length_bounds w).2)
  rw [answer_pad pk w (hlen w) (hsum w)] at hrun
  refine ⟨T,S,Stepped.mapIn_runs hrun,hT.trans hpow,hS.trans hpow,?_⟩
  exact (Nat.cast_le.mpr (LinearPadding.pad_length_bounds w).1).trans (hn.trans hpow)

/-- A fixed composable implementation of exact prime summation with the
original input-length rate. This is the concrete oracle used by prime search. -/
theorem primeSum_stepped :
    ∃ Mc : Stepped (List Bool) (List Bool), Nonempty (IsPolyT Mc) ∧
      ∃ A : ℕ, ∀ w : List Bool, ∃ T S : ℕ,
        Mc.Runs w T S (Nat.bits (primeSum (ofWord w))) ∧
        (T:ℝ)≤(2:ℝ)^T2.Xp A w.length 0 ∧
        (S:ℝ)≤(2:ℝ)^T2.Xp A w.length 0 ∧
        (w.length:ℝ)≤(2:ℝ)^T2.Xp A w.length 0 := by
  obtain ⟨pk,hR,hOk,hsem⟩ := PrimeQueryEnumeration.items_package_exists
  apply stepped_of_package pk hR hOk
  · intro w q hq
    have h := (hsem (precision w) (ofWord w) w (generate_certified _)
      (value_bound w) rfl (precision_le w)).1 q hq
    rwa [hR] at h
  · intro w
    exact (hsem (precision w) (ofWord w) w (generate_certified _)
      (value_bound w) rfl (precision_le w)).2

end PrimeAlgorithm.PrimeSumOracle
