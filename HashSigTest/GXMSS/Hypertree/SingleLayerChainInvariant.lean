/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainInvariant
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Failed first-request ledger controls

A full-signature failure consumes its epoch and retains the actual exhausted retry result.
A later request with a different message cannot replace that log or duplicate its epoch.
The invariant API is available through ordinary public imports.
-/

public section

namespace GXMSS.Hypertree.SingleLayer.ChainInvariantProbe

open Encoding OracleComp OracleSpec
open _root_.GXMSS.Hypertree.Security

/-- One epoch and one bottom chain. -/
@[expose, reducible] def shape : Shape := ⟨1, 0, 1, 1, by decide⟩

/-- The explicit native callback records exhausted retry metadata. -/
@[expose] def attempt (_ : Epoch shape) (_ : Bool) (_ : Unit) :
    IncomparableEncoding.IndexedResult Bool shape.v (2 ^ shape.w) := .exhausted [false]

/-- Full signing fails on each eligible first request. -/
@[expose] def signer (_ : Epoch shape) (_ : Bool) (_ : Unit) :
    Option (Signature Bool Unit shape) := none

/-- A second message at the failed epoch is a rejected repeat. -/
@[expose] def program : OracleComp (ChainMass.FullSpec Bool Unit Bool shape)
    (Option (Signature Bool Unit shape) × Option (Signature Bool Unit shape)) := do
  let first ← (ChainMass.FullSpec Bool Unit Bool shape).query (.inr (0, true))
  let second ← (ChainMass.FullSpec Bool Unit Bool shape).query (.inr (0, false))
  return (first, second)

/-- The consumed failed first message and its private exhausted result remain unchanged. -/
theorem failed_repeat_result :
    (simulateQ (ChainMass.oraclesWithAttempts (pure ()) attempt signer) program).run
        (SyncSignatureUnforgeability.emptyHistory, []) =
      pure ((none, none),
        Function.update SyncSignatureUnforgeability.emptyHistory 0 (some (true, none)),
        [⟨0, true, .exhausted [false]⟩]) := rfl

/-- The actual failed/repeated callback run satisfies history association, coverage and nodup. -/
theorem failed_repeat_invariant :
    AttemptHistoryInvariant (pure ()) attempt signer
      (Function.update SyncSignatureUnforgeability.emptyHistory 0 (some (true, none)),
        [⟨0, true, .exhausted [false]⟩]) := by
  have hinit : AttemptHistoryInvariant (pure ()) attempt signer
      (SyncSignatureUnforgeability.emptyHistory, []) := by
    refine ⟨?_, ?_, ?_⟩
    · intro entry hentry
      simp at hentry
    · intro ep msg answer hentry
      simp [SyncSignatureUnforgeability.emptyHistory] at hentry
    · simp
  have hresult : ((none, none),
      Function.update SyncSignatureUnforgeability.emptyHistory 0 (some (true, none)),
      [⟨0, true, .exhausted [false]⟩]) ∈
      support ((simulateQ (ChainMass.oraclesWithAttempts (pure ()) attempt signer) program).run
        (SyncSignatureUnforgeability.emptyHistory, [])) := by
    rw [failed_repeat_result]
    exact (mem_support_pure_iff _ _).mpr rfl
  exact OracleComp.simulateQ_run_preservesInv _ _
    (oraclesWithAttempts_preserves_attemptHistoryInvariant (pure ()) attempt signer) program
    (SyncSignatureUnforgeability.emptyHistory, []) hinit _ hresult

example := @runFilteredRaw_surviving_invariant
example := @filteredSpliceOracles_preserves_invariant

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``runFilteredRaw_surviving_invariant,
    ``filteredSpliceOracles_preserves_invariant,
    ``oraclesWithAttempts_preserves_attemptHistoryInvariant,
    ``failed_repeat_invariant]

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainInvariant]
    #[(``runFilteredRaw_surviving_invariant,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainInvariant)]
    #[]
    #[(``SpliceStateInvariant,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainInvariant)]

end GXMSS.Hypertree.SingleLayer.ChainInvariantProbe
