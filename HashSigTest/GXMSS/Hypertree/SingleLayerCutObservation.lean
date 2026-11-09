/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutObservation
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Selected-cut observation consumers

Unused and failed-consumed histories preserve the full terminal chain event through ordinary
public imports. The declaration audit checks all coordinate and Boolean observation helpers.
-/

public section

namespace GXMSS.Hypertree.SingleLayer.CutObservationProbe

open Encoding OracleComp OracleSpec TweakableHash

example {PP T X H M R : Type} {h w v : ℕ}
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)))
    (state : Security.NativeState M H R (singleShape h w v))
    (hinv : SpliceStateInvariant (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins state)
    (hrecord : (state.1 forgery.1).bind Prod.snd = none) :
    let ends := Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
      splice.2.1 splice.2.2.val answer starts
    let metadata := Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
      (RetryPlan.iid R J) pp ends upperCoins
    let prefixes := Security.ChainContinuation.splicePrefixes (liftHash hash) pp splice.1
      splice.2.1 splice.2.2.val answer starts
    Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc) pp selector
      (prefixes selector.1 selector.2.1 (selector.2.2.val + 1)) ends metadata
      (Security.ChainContinuation.canonicalReferences metadata prefixes) forgery state =
        GXMSS.Reductions.jointChainObservation hash enc K
          (chainPositionEquiv selector,
            currentSpliceObservation hash pp starts ends forgery state) :=
  selectedCutObservation_no_signature hash enc K J pp selector splice answer starts upperCoins
    forgery state hinv hrecord

example {PP T X H M R : Type} {h w v : ℕ} [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (threshold : ℕ) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (out : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)) ×
        Option (Security.NativeState M H R (singleShape h w v)))
    (hout : out ∈ support (Security.ChainMass.runFilteredRaw (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) adv pp splice.1 splice.2.1 threshold splice.2.2.val answer starts
        upperCoins))
    (state : Security.NativeState M H R (singleShape h w v)) (hstate : out.2 = some state) :
    let ends := Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
      splice.2.1 splice.2.2.val answer starts
    let metadata := Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
      (RetryPlan.iid R J) pp ends upperCoins
    let prefixes := Security.ChainContinuation.splicePrefixes (liftHash hash) pp splice.1
      splice.2.1 splice.2.2.val answer starts
    Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc) pp selector
      (prefixes selector.1 selector.2.1 (selector.2.2.val + 1)) ends metadata
      (Security.ChainContinuation.canonicalReferences metadata prefixes) out.1 state =
        GXMSS.Reductions.jointChainObservation hash enc K
          (chainPositionEquiv selector,
            currentSpliceObservation hash pp starts ends out.1 state) :=
  selectedCutObservation_runFilteredRaw_single hash enc K J adv pp selector splice threshold
    answer starts upperCoins out hout state hstate

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutAlgebra,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutSuccess,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutObservation]
    #[(``selectedCutObservation_splice_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutObservation),
      (``selectedCutObservation_runFilteredRaw_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutObservation),
      (``selectedCutObservation_successful_splice_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutSuccess),
      (``selectedCutObservation_no_signature,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutObservation),
      (``decodeCurrent_single, `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutAlgebra),
      (``cutValidityGuard_current_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutAlgebra)]
    #[] #[]

end GXMSS.Hypertree.SingleLayer.CutObservationProbe
