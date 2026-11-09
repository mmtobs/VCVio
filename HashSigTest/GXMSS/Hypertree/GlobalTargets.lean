/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Global authoritative target consumers

These ordinary consumers use the full forest ledger, exact accepted prefixes and honest-input
orientation. Numeric controls evaluate only small symbolic parameter formulas, never a forest.
The kernel audit includes the shared registration module and both global modules.
-/

public section

namespace GXMSS.Hypertree.GlobalTargetsProbe

open OracleComp TweakableHash GXMSS.Security GXMSS.Reductions
open GXMSS.Hypertree.Unforgeability

/-- A height-three three-layer forest has 3504 chain calls and 1095 Merkle calls. -/
theorem height_three_setup_count :
    let S : Shape := ⟨3, 3, 2, 2, by decide⟩
    chainCount S + treeCount S * (2 * S.branching - 1) = 4599 ∧
      chainCapacity S = 4672 ∧ merkleCapacity S = 9344 := by decide

/-- Height zero retains one hashed leaf per layer in the complete setup count. -/
theorem height_zero_setup_count :
    let S : Shape := ⟨3, 0, 1, 2, by decide⟩
    chainCount S + treeCount S * (2 * S.branching - 1) = 9 := by decide

/-- Width zero removes positive chain calls while retaining every Merkle target. -/
theorem width_zero_setup_count :
    let S : Shape := ⟨3, 1, 0, 1, by decide⟩
    chainCount S = 0 ∧ treeCount S * (2 * S.branching - 1) = 21 ∧
      merkleCapacity S = 28 := by decide

/-- A positive number of chains is necessary for the inherited complete setup capacity. -/
theorem zero_chains_capacity_rejected :
    let S : Shape := ⟨1, 0, 0, 0, by decide⟩
    ¬ chainCount S + treeCount S * (2 * S.branching - 1) ≤ merkleCapacity S := by decide

variable {PP T X H : Type} {S : Shape}

/-- A genuine returned Merkle witness selects its honest first input from the global history,
within the actual global capacity, even when only an authentication path changed. -/
theorem merkle_witness_selection [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (pp : PP) (hv : 0 < S.v)
    (starts ends : OTSPosition S → Fin S.v → H) (p : TreePosition S)
    (ep : Fin S.branching) (ys : Fin S.v → H) (forgedPath : Fin S.h → H)
    (collision : HashCollision T X)
    (hc : (hash.componentHash p).findMerkleCollision pp ep (ends (p, ep)) ys
      ((hash.componentHash p).authPath pp (fun ep => ends (p, ep)) ep) forgedPath =
        some collision) :
    let history := setupLedger hash pp starts ends
    let selected := selectCollision history collision
    history[selected.1]? = some (collision.tweak, collision.first) ∧
      selected.1 < merkleCapacity S ∧
      (match history[selected.1]? with
      | none => False
      | some (t, input) => selected.2 ≠ input ∧
          hash.thf.eval pp t selected.2 = hash.thf.eval pp t input) := by
  have hqueries := ((hash.componentHash p).findMerkleCollision_mem_queries pp ep
    (ends (p, ep)) ys ((hash.componentHash p).authPath pp (fun ep => ends (p, ep)) ep)
    forgedPath hc).1
  have hmem := merkleOpeningTarget_mem_setupLedger hash pp starts ends p ep
    (collision.tweak, collision.first) hqueries
  have hsound : collision.Sound hash.thf pp := by
    simpa only [HashInstance.componentHash_thf] using
      (hash.componentHash p).findMerkleCollision_sound pp ep (ends (p, ep)) ys
        ((hash.componentHash p).authPath pp (fun ep => ends (p, ep)) ep) forgedPath hc
  exact ⟨selectCollision_lookup _ _ hmem,
    selectCollision_index_lt _ _ _ hmem (by simpa using setupCount_le_capacity S hv),
    selectCollision_valid hash pp _ collision hmem hsound⟩

/-- The collision extractor's second phase is a native computation with no challenge oracle. -/
noncomputable example [SampleableType H] [DecidableEq T] [DecidableEq X]
    (hash : HashInstance PP T X H S)
    (extract : ForestSetupState T X H S → PP → ProbComp (HashCollision T X))
    (state : ForestSetupState T X H S) (pp : PP) : ProbComp (ℕ × X) :=
  (merkleCollisionAdversary hash extract).forge state pp

example := @registerChains_run
example := @registerMerkle_run
example := @registerForest_run
example := @chooseChains_run
example := @chooseForest_run
example := @chainLedger_prefix_accepted
example := @setupLedger_prefix_accepted
example := @chainTarget_mem_chainLedger

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``height_three_setup_count, ``height_zero_setup_count, ``width_zero_setup_count,
    ``zero_chains_capacity_rejected, ``merkle_witness_selection]

run_cmd Lean.Elab.Command.liftTermElabM do
  let modules := #[`HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation,
    `HashSig.GXMSS.Security.Hypertree.Auxiliary.TargetCounts,
    `HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration]
  let endpoints := #[(``tcrBlocks_run,
      `HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation),
    (``chainLedger_length, `HashSig.GXMSS.Security.Hypertree.Auxiliary.TargetCounts),
    (``setupLedger_length, `HashSig.GXMSS.Security.Hypertree.Auxiliary.TargetCounts),
    (``setupLedger_tweaks_nodup, `HashSig.GXMSS.Security.Hypertree.Auxiliary.TargetCounts),
    (``registerForest_run, `HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration),
    (``chooseChains_run, `HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration),
    (``chooseForest_run, `HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration),
    (``selectCollision_valid, `HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration)]
  let definitions := #[(``chainLedger,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.TargetCounts),
    (``registerForest, `HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration),
    (``chainCollisionAdversary, `HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration),
    (``merkleCollisionAdversary, `HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration)]
  GXMSS.Test.TrustAudit.check modules endpoints #[] definitions

end GXMSS.Hypertree.GlobalTargetsProbe
