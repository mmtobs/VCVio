/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Complete depth-one chain experiment consumers

A successful total PRE fallback wins independently of validity or filter survival.
The public Boolean equation retains that mass instead of replacing it with selected-cut mass.
-/

public section

namespace GXMSS.Hypertree.SingleLayer.ChainExperimentProbe

open Encoding OracleComp OracleSpec TweakableHash

example {PP T X H M R : Type} {h w v : ℕ}
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sampling : RetrySampling R)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) (pp : PP)
    (selector : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → sampling.internal.Coins) (hv : 0 < v)
    (hfall : hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector))
      (hash.digestInput (startsEquiv starts 0 ⟨0, hv⟩)) = answer) :
    (fun preimage => decide (hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector))
      (hash.digestInput preimage) = answer)) <$>
      Security.invertAt (liftHash hash) (familyOfEncoding enc) sampling adv pp selector answer
        starts upperCoins =ᵈ (pure true : ProbComp Bool) := by
  rw [invertAt_boolean_single, canonicalPreimageFallback_single starts hv]
  simp only [hfall, decide_true, Bool.true_or]
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    (EvalDistEq.bind_const _ (pure true))

section CompleteGames

variable {PP T X H M R : Type} {h w v : ℕ}
variable [SampleableType H] [SampleableType R]
variable [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
variable [DecidableEq (GXMSS.Signature R H h v)]
variable (hash : GXMSS.HashInstance PP T X H h w v)
variable (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
variable (hv : 0 < v) (hw : 0 < w)
variable (adv : Security.SchemeAdversary PP H M R (singleShape h w v))

example :
    SM_DT_PRE_Experiment (Security.chainPreimageReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) hv hw adv) =ᵈ
    SM_DT_PRE_Experiment (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw
      (adversaryToOrdinary adv)) :=
  chainPREExperiment_single hash enc K J hv hw adv

example :
    SM_DT_UD_Experiment .real (Security.chainUndetectabilityReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) hv hw adv
      (Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc))) =ᵈ
    SM_DT_UD_Experiment .real (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw
      (adversaryToOrdinary adv)) :=
  chainUDExperiment_single hash enc K J hv hw adv .real

example :
    SM_DT_UD_Experiment .ideal (Security.chainUndetectabilityReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) hv hw adv
      (Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc))) =ᵈ
    SM_DT_UD_Experiment .ideal (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw
      (adversaryToOrdinary adv)) :=
  chainUDExperiment_single hash enc K J hv hw adv .ideal

example :
    SM_DT_PRE_Advantage (Security.chainPreimageReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) hv hw adv) =
    SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw
      (adversaryToOrdinary adv)) :=
  chainPREAdvantage_single hash enc K J hv hw adv

example :
    SM_DT_UD_Advantage (Security.chainUndetectabilityReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) hv hw adv
      (Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc))) =
    SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw
      (adversaryToOrdinary adv)) :=
  chainUDAdvantage_single hash enc K J hv hw adv

end CompleteGames

example := @bottomResult_iid_single
example := @privateBad_single
example := @disclosedBad_single
example := @invertAt_boolean_single

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments]
    #[(``invertAt_boolean_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments),
      (``chainPREExperiment_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments),
      (``chainPREAdvantage_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments),
      (``chainUDExperiment_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments),
      (``chainUDAdvantage_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments)]
    #[]
    #[(``spliceResultObservation,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames)]

end GXMSS.Hypertree.SingleLayer.ChainExperimentProbe
