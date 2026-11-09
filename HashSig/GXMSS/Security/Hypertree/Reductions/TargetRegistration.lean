/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Scheme
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.TargetCounts
import all HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation

/-!
# Authoritative global target registration

The choose computations have no public-seed input. They use the existing component chain and
Merkle registrations under one authoritative SM-DT-TCR history. The public seed appears only in
simulation statements and in the subsequent oracle-free collision extraction interface.
-/

public section

namespace GXMSS.Hypertree.Unforgeability

open OracleComp OracleSpec TweakableHash GXMSS.Reductions

variable {PP T X H : Type} {S : Shape}

/-- The authoritative challenge interface with private randomness and an empty collection. -/
abbrev RegistrationSpec (hash : HashInstance PP T X H S) (targets : ℕ) :=
  unifSpec + (SM_DT_TCR_challengeSpec T X H +
    collectionSpec (SM_DT_TCR_Problem.standalone hash.thf targets).thColl)

/-- State and oracle signature used by the single global registration interaction. -/
abbrev SetupM (hash : HashInstance PP T X H S) (targets : ℕ) :=
  StateT (List (T × X)) (OracleComp (RegistrationSpec hash targets))

/-- Restrict a full forest start table to one component. -/
@[expose] def componentStarts (starts : OTSPosition S → Fin S.v → H)
    (p : TreePosition S) : Fin S.branching → Fin S.v → H := fun ep => starts (p, ep)

/-- Register all forest chains before revealing the seed, using the fixed component order. -/
@[expose] noncomputable def registerChains (hash : HashInstance PP T X H S) (targets : ℕ)
    (starts : OTSPosition S → Fin S.v → H) (fallback : H) :
    SetupM hash targets (Fin (treeCount S) → Fin S.branching → Fin S.v → H) :=
  Fin.mOfFn (treeCount S) fun a => tcrEndpoints
    (hash.componentHash (componentEnumeration S a)) targets
    (componentStarts starts (componentEnumeration S a)) fallback

/-- Convert the ordered component results back to the full one-time-key coordinate domain. -/
@[expose] noncomputable def materializeEndpoints
    (values : Fin (treeCount S) → Fin S.branching → Fin S.v → H) :
    OTSPosition S → Fin S.v → H :=
  fun p => values ((componentEnumeration S).symm p.1) p.2

/-- Register full component Merkle trees under the same global history and component order. -/
@[expose] noncomputable def registerMerkle (hash : HashInstance PP T X H S) (targets : ℕ)
    (ends : OTSPosition S → Fin S.v → H) (fallback : H) :
    SetupM hash targets (Fin (treeCount S) → H) :=
  Fin.mOfFn (treeCount S) fun a => tcrMerkleRoot
    (hash.componentHash (componentEnumeration S a)) targets
    (componentStarts ends (componentEnumeration S a)) fallback

/-- Convert roots in issue order back to component coordinates. -/
@[expose] noncomputable def materializeRoots (values : Fin (treeCount S) → H) :
    TreePosition S → H := fun p => values ((componentEnumeration S).symm p)

/-- Register every chain and then every component Merkle tree, without access to the seed. -/
@[expose] noncomputable def registerForest (hash : HashInstance PP T X H S) (targets : ℕ)
    (starts : OTSPosition S → Fin S.v → H) (fallback : H) :
    SetupM hash targets ((OTSPosition S → Fin S.v → H) × (TreePosition S → H)) := do
  let values ← registerChains hash targets starts fallback
  let ends := materializeEndpoints values
  let roots ← registerMerkle hash targets ends fallback
  pure (ends, materializeRoots roots)

/-- Global chain registration reproduces every ordinary component endpoint and the exact ledger. -/
theorem registerChains_run [DecidableEq T]
    (hash : HashInstance PP T X H S) (targets : ℕ) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (fallback : H) (history : List (T × X))
    (hcap : history.length + chainCount S ≤ targets)
    (hfresh : ∀ p ep i j, ∀ q ∈ history,
      q.1 ≠ (hash.componentHash p).chainTweak (ep, i, j)) :
    ((simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((registerChains hash targets starts fallback).run history)).run (history, [])) =
      pure ((((fun a : Fin (treeCount S) =>
        GXMSS.endpoints (hash.componentHash (componentEnumeration S a)) pp
          (componentStarts starts (componentEnumeration S a))),
        history ++ chainLedger hash pp starts), history ++ chainLedger hash pp starts, [])) := by
  apply tcrBlocks_run (hash.componentHash (topTree S)) targets pp (treeCount S)
    (S.branching * S.v * (2 ^ S.w - 1)) _ _
    (fun a => componentChainTargets hash pp starts (componentEnumeration S a))
  · intro a
    simp [componentChainTargets]
  · intro a b hab
    exact componentChainTargets_disjoint hash pp starts _ _
      (fun heq => hab ((componentEnumeration S).injective heq))
  · intro a previous hprevious hfreshPrevious
    apply tcrEndpoints_run (hash.componentHash (componentEnumeration S a)) targets pp
      (componentStarts starts (componentEnumeration S a)) fallback previous hprevious
    intro ep i j q hq
    exact hfreshPrevious q hq
      ((hash.componentHash (componentEnumeration S a)).chainTweak (ep, i, j),
        hash.digestInput ((hash.componentHash (componentEnumeration S a)).chain pp ep i 0 j.val
          (starts (componentEnumeration S a, ep) i)))
      (chainTarget_mem_endpointTargets _ _ _ ep i j)
  · simpa [chainCount, otsCount, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcap
  · intro a q hq r hr
    obtain ⟨ep, i, j, heq⟩ := endpointTarget_tweak _ _ _ hr
    rw [heq]
    exact hfresh _ ep i j q hq

/-- Materialized accepted component endpoints equal the ordinary full forest endpoint table. -/
theorem materializeEndpoints_eq (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) :
    materializeEndpoints (fun a : Fin (treeCount S) =>
      GXMSS.endpoints (hash.componentHash (componentEnumeration S a)) pp
        (componentStarts starts (componentEnumeration S a))) = endpoints hash pp starts := by
  funext p i
  simp [materializeEndpoints, GXMSS.endpoints, endpoints, componentStarts]

/-- Global Merkle registration reproduces ordinary component roots and the exact ordered ledger. -/
theorem registerMerkle_run [DecidableEq T]
    (hash : HashInstance PP T X H S) (targets : ℕ) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) (fallback : H) (history : List (T × X))
    (hcap : history.length + treeCount S * (2 * S.branching - 1) ≤ targets)
    (hfresh : ∀ p, ∀ q ∈ history, ∀ r ∈ componentMerkleTargets hash pp ends p, q.1 ≠ r.1) :
    ((simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((registerMerkle hash targets ends fallback).run history)).run (history, [])) =
      pure ((((fun a : Fin (treeCount S) =>
        componentRoot hash pp ends (componentEnumeration S a)),
        history ++ merkleLedger hash pp ends), history ++ merkleLedger hash pp ends, [])) := by
  apply tcrBlocks_run (hash.componentHash (topTree S)) targets pp (treeCount S)
    (2 * S.branching - 1) _ _
    (fun a => componentMerkleTargets hash pp ends (componentEnumeration S a))
  · intro a
    simp [componentMerkleTargets, Shape.branching, pow_succ, Nat.mul_comm]
  · intro a b hab
    exact componentMerkleTargets_disjoint hash pp ends _ _
      (fun heq => hab ((componentEnumeration S).injective heq))
  · intro a previous hprevious hfreshPrevious
    apply tcrMerkleRoot_run (hash.componentHash (componentEnumeration S a)) targets pp
      (componentStarts ends (componentEnumeration S a)) fallback previous
    · simpa [Shape.branching, pow_succ, Nat.mul_comm] using hprevious
    · exact hfreshPrevious
  · exact hcap
  · intro a
    exact hfresh (componentEnumeration S a)

/-- Materialized accepted component roots equal their ordinary deterministic root family. -/
theorem materializeRoots_eq (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) :
    materializeRoots (fun a : Fin (treeCount S) =>
      componentRoot hash pp ends (componentEnumeration S a)) = componentRoot hash pp ends := by
  funext p
  simp [materializeRoots]

/-- Complete seed-free registration returns ordinary forest key data and the exact authoritative
chain-first setup history, with no rejected target or collection use. -/
theorem registerForest_run [DecidableEq T]
    (hash : HashInstance PP T X H S) (targets : ℕ) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (fallback : H)
    (hcap : chainCount S + treeCount S * (2 * S.branching - 1) ≤ targets) :
    ((simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      ((registerForest hash targets starts fallback).run [])).run ([], [])) =
      let ends := endpoints hash pp starts
      let registered := setupLedger hash pp starts ends
      pure ((((ends, componentRoot hash pp ends), registered), registered, [])) := by
  have hchain : chainCount S ≤ targets := by omega
  simp only [registerForest, StateT.run_bind, simulateQ_bind]
  rw [registerChains_run hash targets pp starts fallback [] (by simpa using hchain)
    (by simp)]
  simp only [pure_bind, List.nil_append, materializeEndpoints_eq]
  rw [registerMerkle_run hash targets pp (endpoints hash pp starts) fallback
    (chainLedger hash pp starts)]
  · simp [materializeRoots_eq, setupLedger]
  · simpa using hcap
  · intro p q hq r hr
    exact chainLedger_merkleLedger_disjoint hash pp starts (endpoints hash pp starts)
      q hq r (componentMerkleTarget_mem_merkleLedger hash pp _ p hr)

/-- Private state retained by a chain-target chooser before seed revelation. -/
structure ChainSetupState (T X H : Type) (S : Shape) where
  /-- Independently sampled full forest starts. -/
  starts : OTSPosition S → Fin S.v → H
  /-- Endpoints returned by the authoritative chain registrations. -/
  endpoints : OTSPosition S → Fin S.v → H
  /-- Exact locally recorded accepted challenge targets. -/
  targets : List (T × X)
  /-- Internal fallback retained for total rejected-query behavior. -/
  fallback : H

/-- Private state of a chooser that also registers all component Merkle trees. -/
structure ForestSetupState (T X H : Type) (S : Shape) extends ChainSetupState T X H S where
  /-- All component roots returned by authoritative Merkle registration. -/
  roots : TreePosition S → H

/-- Sample and register every forest chain without obtaining the public seed. -/
@[expose] noncomputable def chooseChains [SampleableType H]
    (hash : HashInstance PP T X H S) (targets : ℕ) :
    OracleComp (RegistrationSpec hash targets) (ChainSetupState T X H S) := do
  let fallback ← OracleComp.liftComp ($ᵗ H) _
  let starts ← OracleComp.liftComp (sampleStarts S) _
  let (values, registered) ← (registerChains hash targets starts fallback).run []
  pure ⟨starts, materializeEndpoints values, registered, fallback⟩

/-- Sample and register the complete forest without obtaining the public seed. -/
@[expose] noncomputable def chooseForest [SampleableType H]
    (hash : HashInstance PP T X H S) (targets : ℕ) :
    OracleComp (RegistrationSpec hash targets) (ForestSetupState T X H S) := do
  let fallback ← OracleComp.liftComp ($ᵗ H) _
  let starts ← OracleComp.liftComp (sampleStarts S) _
  let ((ends, roots), registered) ← (registerForest hash targets starts fallback).run []
  pure ⟨⟨starts, ends, registered, fallback⟩, roots⟩

private theorem simulate_uniform_run [DecidableEq T]
    (hash : HashInstance PP T X H S) (targets : ℕ) (pp : PP) {A : Type}
    (oa : ProbComp A) (state : SM_DT_TCR_State T X) :
    (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      (OracleComp.liftComp oa _)).run state = (fun value => (value, state)) <$> oa := by
  rw [SM_DT_TCR_oracles, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget,
    simulateQ_ofLift_eq_self]
  simp

/-- The chain chooser's local targets are precisely the accepted global authoritative history. -/
theorem chooseChains_run [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H S) (targets : ℕ) (pp : PP)
    (hcap : chainCount S ≤ targets) :
    (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      (chooseChains hash targets)).run ([], []) = (do
        let fallback ← ($ᵗ H : ProbComp H)
        let starts ← sampleStarts S
        let registered := chainLedger hash pp starts
        pure ((⟨starts, endpoints hash pp starts, registered, fallback⟩ :
          ChainSetupState T X H S), registered, [])) := by
  simp only [chooseChains, simulateQ_bind, StateT.run_bind]
  rw [simulate_uniform_run, bind_map_left]
  apply bind_congr
  intro fallback
  rw [simulate_uniform_run, bind_map_left]
  apply bind_congr
  intro starts
  rw [registerChains_run hash targets pp starts fallback [] (by simpa using hcap) (by simp)]
  simp [materializeEndpoints_eq]

/-- The full chooser's local targets and roots equal the exact authoritative setup computation. -/
theorem chooseForest_run [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H S) (targets : ℕ) (pp : PP)
    (hcap : chainCount S + treeCount S * (2 * S.branching - 1) ≤ targets) :
    (simulateQ (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf targets) pp)
      (chooseForest hash targets)).run ([], []) = (do
        let fallback ← ($ᵗ H : ProbComp H)
        let starts ← sampleStarts S
        let ends := endpoints hash pp starts
        let registered := setupLedger hash pp starts ends
        pure ((⟨⟨starts, ends, registered, fallback⟩, componentRoot hash pp ends⟩ :
          ForestSetupState T X H S), registered, [])) := by
  simp only [chooseForest, simulateQ_bind, StateT.run_bind]
  rw [simulate_uniform_run, bind_map_left]
  apply bind_congr
  intro fallback
  rw [simulate_uniform_run, bind_map_left]
  apply bind_congr
  intro starts
  rw [registerForest_run hash targets pp starts fallback hcap]
  simp

/-- Select the registered honest first input and return the extracted second collision input. -/
@[expose] def selectCollision [DecidableEq T] [DecidableEq X]
    (history : List (T × X)) (collision : GXMSS.Security.HashCollision T X) : ℕ × X :=
  (registeredIndex history collision.tweak collision.first, collision.second)

/-- The chain collision chooser uses the inherited global chain capacity and reveals the public
seed only to an oracle-free extractor. -/
@[expose] noncomputable def chainCollisionAdversary [SampleableType H]
    [DecidableEq T] [DecidableEq X] (hash : HashInstance PP T X H S)
    (extract : ChainSetupState T X H S → PP → ProbComp (GXMSS.Security.HashCollision T X)) :
    SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone hash.thf (chainCapacity S)) where
  State := ChainSetupState T X H S
  choose := chooseChains hash (chainCapacity S)
  forge state pp := selectCollision state.targets <$> extract state pp

/-- The Merkle collision chooser uses the inherited global setup capacity and reveals the public
seed only to an oracle-free extractor. -/
@[expose] noncomputable def merkleCollisionAdversary [SampleableType H]
    [DecidableEq T] [DecidableEq X] (hash : HashInstance PP T X H S)
    (extract : ForestSetupState T X H S → PP → ProbComp (GXMSS.Security.HashCollision T X)) :
    SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone hash.thf (merkleCapacity S)) where
  State := ForestSetupState T X H S
  choose := chooseForest hash (merkleCapacity S)
  forge state pp := selectCollision state.targets <$> extract state pp

/-- Membership identifies the exact honest first input at the selected global index. -/
theorem selectCollision_lookup [DecidableEq T] [DecidableEq X]
    (history : List (T × X)) (collision : GXMSS.Security.HashCollision T X)
    (hmem : (collision.tweak, collision.first) ∈ history) :
    history[(selectCollision history collision).1]? = some (collision.tweak, collision.first) :=
  registeredIndex_lookup_of_mem history collision.tweak collision.first hmem

/-- Every selected registered input lies within any capacity covering the actual history. -/
theorem selectCollision_index_lt [DecidableEq T] [DecidableEq X]
    (history : List (T × X)) (collision : GXMSS.Security.HashCollision T X) (capacity : ℕ)
    (hmem : (collision.tweak, collision.first) ∈ history) (hcap : history.length ≤ capacity) :
    (selectCollision history collision).1 < capacity :=
  registeredIndex_lt_capacity_of_mem history collision.tweak collision.first capacity hmem hcap

/-- The actual SM-DT-TCR check has the required orientation: registered honest input first,
distinct colliding extracted input second. -/
theorem selectCollision_valid [DecidableEq T] [DecidableEq X]
    (hash : HashInstance PP T X H S) (pp : PP) (history : List (T × X))
    (collision : GXMSS.Security.HashCollision T X)
    (hmem : (collision.tweak, collision.first) ∈ history)
    (hsound : collision.Sound hash.thf pp) :
    match history[(selectCollision history collision).1]? with
    | none => False
    | some (t, input) => (selectCollision history collision).2 ≠ input ∧
        hash.thf.eval pp t (selectCollision history collision).2 = hash.thf.eval pp t input := by
  rw [selectCollision_lookup history collision hmem]
  exact ⟨hsound.1.symm, hsound.2.symm⟩

/-- Every member of a nonrepeating, within-cap issue schedule is accepted after its exact prefix. -/
theorem target_prefix_accepted [DecidableEq T]
    (hash : HashInstance PP T X H S) (targets : ℕ) (pp : PP)
    (schedule before after : List (T × X)) (target : T × X)
    (hsplit : schedule = before ++ target :: after)
    (hnodup : (schedule.map Prod.fst).Nodup) (hcap : schedule.length ≤ targets) :
    (SM_DT_TCR_challengeOracle (SM_DT_TCR_Problem.standalone hash.thf targets) pp target).run
      (before, []) = pure (some (hash.thf.eval pp target.1 target.2), before ++ [target], []) := by
  have hbelow : before.length < targets := by
    rw [hsplit] at hcap
    simp only [List.length_append, List.length_cons] at hcap
    omega
  have hfresh : TweakFresh Prod.fst before [] target.1 := by
    have h := tweakFresh_of_target_prefix [] before after target (by simp)
      (by rw [← hsplit]; exact hnodup)
    simpa using h
  exact SM_DT_TCR_challengeOracle_run_of_fresh hbelow hfresh

/-- Every global positive-chain registration is accepted at its exact chain-capacity prefix. -/
theorem chainLedger_prefix_accepted [DecidableEq T]
    (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (before after : List (T × X)) (target : T × X)
    (hsplit : chainLedger hash pp starts = before ++ target :: after) :
    (SM_DT_TCR_challengeOracle (SM_DT_TCR_Problem.standalone hash.thf (chainCapacity S))
      pp target).run (before, []) =
        pure (some (hash.thf.eval pp target.1 target.2), before ++ [target], []) :=
  target_prefix_accepted hash _ pp _ before after target hsplit
    (chainLedger_tweaks_nodup hash pp starts) (by simpa using chainCount_le_capacity S)

/-- Every global chain or Merkle registration is accepted at the exact setup-capacity prefix. -/
theorem setupLedger_prefix_accepted [DecidableEq T]
    (hash : HashInstance PP T X H S) (pp : PP) (hv : 0 < S.v)
    (starts ends : OTSPosition S → Fin S.v → H)
    (before after : List (T × X)) (target : T × X)
    (hsplit : setupLedger hash pp starts ends = before ++ target :: after) :
    (SM_DT_TCR_challengeOracle (SM_DT_TCR_Problem.standalone hash.thf (merkleCapacity S))
      pp target).run (before, []) =
        pure (some (hash.thf.eval pp target.1 target.2), before ++ [target], []) :=
  target_prefix_accepted hash _ pp _ before after target hsplit
    (setupLedger_tweaks_nodup hash pp starts ends) (by simpa using setupCount_le_capacity S hv)

end GXMSS.Hypertree.Unforgeability
