/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainCollision
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Exact depth-one B2 consumer

The ordinary consumer uses both named reductions and their complete Boolean experiment.
The audit traverses every helper body, including the source/reference and fallback transports.
-/

public section

namespace GXMSS.Hypertree.SingleLayer.ChainCollisionProbe

open Encoding OracleComp OracleSpec TweakableHash
open GXMSS.Hypertree.Unforgeability

example {PP T X H M R : Type} {h w v : ℕ} [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Experiment (chainCutTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) adv) =ᵈ
      SM_DT_TCR_Experiment (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K
        (adversaryToOrdinary adv)) :=
  chainCutTargetCollisionExperiment_single hash enc K J adv

example := @chainCutTargetCollisionAdvantage_single

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainCollision]
    #[(``chainCutTargetCollisionExperiment_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainCollision),
      (``chainCutTargetCollisionAdvantage_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainCollision)]
    #[]
    #[]

end GXMSS.Hypertree.SingleLayer.ChainCollisionProbe
