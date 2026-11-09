/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainObservation
meta import HashSigTest.GXMSS.TrustAuditSupport

/-! # Public successful-history observations of actual filtered splice runs -/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp

variable {PP T X H M R : Type} {h w v : ℕ}

example [SampleableType R] (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (pp : PP) (splice : ChainPosition (singleShape h w v)) (threshold : ℕ) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (coins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (out : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
        (Signature R H (singleShape h w v)) ×
      Option (Security.NativeState M H R (singleShape h w v)))
    (state : Security.NativeState M H R (singleShape h w v))
    (hout : out ∈ support (Security.ChainMass.runFilteredRaw (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) adv pp splice.1 splice.2.1 threshold
        splice.2.2.val answer starts coins))
    (hstate : out.2 = some state)
    (ep : Epoch (singleShape h w v)) (msg : M) (sig : Signature R H (singleShape h w v))
    (hrecord : state.1 ep = some (msg, some sig)) :
    ∃ word, enc.value pp msg sig.bottom.randomizer (epochEquiv ep) = some word ∧
      ∀ i, sig.bottom.ots i = Security.ChainContinuation.splicePrefixes (liftHash hash) pp
        splice.1 splice.2.1 splice.2.2.val answer starts (bottomPosition _ ep) i (word i).val := by
  have hinv := runFilteredRaw_surviving_invariant (liftHash hash) (familyOfEncoding enc)
    (RetrySampling.iid K J) adv pp splice.1 splice.2.1 threshold splice.2.2.val answer starts
      coins out hout state hstate
  obtain ⟨word, hword, hcomponent⟩ := successful_splice_history_component hash enc K J pp
    splice answer starts coins state hinv ep msg sig hrecord
  refine ⟨word, hword, fun i => ?_⟩
  exact congrArg (fun signature : GXMSS.Signature R H h v => signature.ots i) hcomponent

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``referenceResult_bottom_eq_history,
    ``referenceResult_bottom_splice_single,
    ``successful_splice_history_component]

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainObservation]
    #[(``referenceResult_bottom_eq_history,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainObservation),
      (``referenceResult_bottom_splice_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainObservation),
      (``successful_splice_history_component,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainObservation)]
    #[]

end GXMSS.Hypertree.SingleLayer
