/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.SingleLayer
public import HashSig.GXMSS.Security.Hypertree.SingleLayer
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Single-layer ordinary consumers

The bridge preserves raw keys, arbitrary signature verification and optional IID signing.
Coordinate and coefficient controls include zero height and zero chain dimensions.
-/

public section

namespace GXMSS.Hypertree.SingleLayerProbe

open GXMSS.Hypertree.SingleLayer

example : treeCount (singleShape 3 2 2) = 1 := by decide
example : otsCount (singleShape 3 2 2) = 8 := by decide
example : upperCount (singleShape 3 2 2) = 0 := by decide
example : chainCount (singleShape 3 2 2) = 48 := by decide
example : chainCount (singleShape 0 0 0) = 0 := by decide
example : Nat.card (UpperPosition (singleShape 3 2 2)) = 0 := by
  rw [card_upperPosition]
  decide

variable {PP T X H M R : Type} {h w v : ℕ}

/-- An ordinary consumer restricts every lifted component to the original hash interface. -/
theorem old_hash_recovered (hash : GXMSS.HashInstance PP T X H h w v)
    (p : TreePosition (singleShape h w v)) : (liftHash hash).componentHash p = hash :=
  componentHash_liftHash hash p

example := @verify_eq
example := @signWithCoins_iid_eq
example := @sign_iid_evalDistEq
example := @sampleStarts_evalDistEq
example := @keygen_evalDistEq
example := @chainLedger_single
example := @setupLedger_single
example := @merkleFallbackInput_single
example := @sourceMerkleWitness?_single
example := @collisionProgram_source_evalDistEq
example := @sourceProgram_iid_evalDistEq
example := @merkleTargetCollisionExperiment_single
example := @merkleTargetCollisionAdvantage_single
example := @sameMessageChainTargetCollisionExperiment_single
example := @sameMessageChainTargetCollisionAdvantage_single
example := @merkleTargetCollisionExperiment_full_single
example := @sameMessageChainTargetCollisionExperiment_full_single

run_cmd Lean.Elab.Command.liftTermElabM do
  let modules := #[`HashSig.GXMSS.Hypertree.SingleLayer,
    `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource,
    `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames]
  let endpoints := #[(``verify_eq, `HashSig.GXMSS.Hypertree.SingleLayer),
    (``sign_iid_evalDistEq, `HashSig.GXMSS.Hypertree.SingleLayer),
    (``keygen_evalDistEq, `HashSig.GXMSS.Hypertree.SingleLayer),
    (``sourceProgram_iid_evalDistEq,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource),
    (``merkleTargetCollisionExperiment_single,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames),
    (``sameMessageChainTargetCollisionExperiment_single,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames),
    (``setupLedger_single, `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames),
    (``collisionProgram_source_evalDistEq,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames)]
  let definitions := #[(``liftHash, `HashSig.GXMSS.Hypertree.SingleLayer),
    (``signatureEquiv, `HashSig.GXMSS.Hypertree.SingleLayer),
    (``secretKeyEquiv, `HashSig.GXMSS.Hypertree.SingleLayer),
    (``familyOfEncoding, `HashSig.GXMSS.Hypertree.SingleLayer)]
  GXMSS.Test.TrustAudit.check modules endpoints #[] definitions

end GXMSS.Hypertree.SingleLayerProbe
