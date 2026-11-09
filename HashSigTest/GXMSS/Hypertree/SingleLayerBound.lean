/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Depth-one bound compatibility consumers

The public interface exposes actual named full-range experiments and the separate sharp to
complete-tree coefficient relaxation.
-/

public section

namespace GXMSS.Hypertree.SingleLayer.BoundProbe

open Encoding OracleComp OracleSpec TweakableHash
open GXMSS.Hypertree.Unforgeability

example {PP T X H M R : Type} {h w v : ℕ} [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    Security.FamilyEncoding.experiment (Security.encodingTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) qs adv) =ᵈ
      TargetCollisionResistance.experiment
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction hash enc qs K
          (GXMSS.IntervalMerkle.Interval.full h) (adversaryToOrdinary adv)) :=
  encodingTargetCollisionExperiment_full_single hash enc qs K J adv hqueries

example := @chainCutTargetCollisionExperiment_full_single
example := @sharp_reduction_bound_le_complete

example {PP T X H M R : Type} {h w v : ℕ} [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_PRE_Experiment (Security.chainPreimageReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) hv hw adv) =ᵈ
      SM_DT_PRE_Experiment (GXMSS.Interval.Reductions.Chain.chainPreimageReduction
        hash enc K (GXMSS.IntervalMerkle.Interval.full h) hv hw (adversaryToOrdinary adv)) :=
  chainPREExperiment_full_single hash enc K J hv hw adv

example {PP T X H M R : Type} {h w v : ℕ} [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (Security.chainUndetectabilityReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) hv hw adv
      (Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc))) =ᵈ
      SM_DT_UD_Experiment world (GXMSS.Interval.Reductions.Chain.chainUndetectabilityReduction
        hash enc K (GXMSS.IntervalMerkle.Interval.full h) hv hw (adversaryToOrdinary adv)) :=
  chainUDExperiment_full_single hash enc K J hv hw adv world

example {PP T X H M R : Type} {h w v : ℕ} [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    strongUnforgeabilityBound (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      qs hv hw adv =
      GXMSS.Interval.Unforgeability.strongUnforgeabilityBound hash enc K qs
        (GXMSS.IntervalMerkle.Interval.full h) hv hw (adversaryToOrdinary adv) :=
  strongUnforgeabilityBound_eq_interval_full hash enc K J qs hv hw adv hqueries

example {PP T X H M R : Type} {h w v : ℕ} [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [DecidableEq (Signature R H (singleShape h w v))]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J qs : ℕ)
    (hv : 0 < v) (hw : 0 < w) (hnonmax : (familyOfEncoding (H := H) enc).NoMaximumOutput)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    SyncSignatureUnforgeability.strongAdvantage
      (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J))
      ProbCompRuntime.probComp adv ≤
      GXMSS.Unforgeability.reductionBound h w v
        (SM_DT_TCR_Advantage (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv
          (adversaryToOrdinary adv)))
        (TargetCollisionResistance.advantage (GXMSS.Reductions.encodingTargetCollisionReduction
          hash enc qs K (adversaryToOrdinary adv)))
        (SM_DT_TCR_Advantage (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K
          (adversaryToOrdinary adv)))
        (SM_DT_TCR_Advantage (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K
          (adversaryToOrdinary adv)))
        (SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw
          (adversaryToOrdinary adv)))
        (SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw
          (adversaryToOrdinary adv))) :=
  strong_unforgeability_relaxed_complete hash enc K J qs hv hw hnonmax adv hqueries

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound]
    #[(``encodingTargetCollisionExperiment_full_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound),
      (``chainCutTargetCollisionExperiment_full_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound),
      (``chainPREExperiment_full_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound),
      (``chainUDExperiment_full_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound),
      (``strongUnforgeabilityBound_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound),
      (``strongUnforgeabilityBound_eq_interval_full,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound),
      (``strongUnforgeabilityBound_single_le_complete,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound),
      (``strong_unforgeability_relaxed_complete,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound),
      (``sharp_reduction_bound_le_complete,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound)]
    #[] #[]

end GXMSS.Hypertree.SingleLayer.BoundProbe
