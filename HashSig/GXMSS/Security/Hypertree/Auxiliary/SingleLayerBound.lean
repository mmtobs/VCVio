/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainCollision
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments
public import HashSig.GXMSS.Security.Hypertree.Unforgeability
public import HashSig.GXMSS.Security.Unforgeability

/-!
# Depth-one security-bound compatibility

The named global reductions retain the full-range interval games and their exact sharp
positive-position coefficients. The complete-tree power-of-two bound is a separate relaxation.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding ENNReal OracleComp OracleSpec TweakableHash
open GXMSS.Hypertree.Unforgeability

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The named global encoding experiment preserves the full-range interval experiment, with the
same exact signing-query bound used by the native security theorem. -/
theorem encodingTargetCollisionExperiment_full_single [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    Security.FamilyEncoding.experiment (Security.encodingTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) qs adv) =ᵈ
      TargetCollisionResistance.experiment
        (GXMSS.Interval.Reductions.encodingTargetCollisionReduction hash enc qs K
          (GXMSS.IntervalMerkle.Interval.full h) (adversaryToOrdinary adv)) := by
  rw [GXMSS.Interval.Unforgeability.encodingTargetCollisionExperiment_full]
  exact EncodingTransport.historical_reduction_experiment_evalDistEq hash enc qs K J adv hqueries

/-- The named global B2 experiment preserves the retained full-range interval experiment. -/
theorem chainCutTargetCollisionExperiment_full_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Experiment (chainCutTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) adv) =ᵈ
      SM_DT_TCR_Experiment (GXMSS.Interval.Reductions.Chain.chainCutTargetCollisionReduction
        hash enc K (GXMSS.IntervalMerkle.Interval.full h) (adversaryToOrdinary adv)) := by
  rw [GXMSS.Interval.Unforgeability.chainCutTargetCollisionExperiment_full]
  exact chainCutTargetCollisionExperiment_single hash enc K J adv

/-- The exact positive-position coefficients are bounded by the complete-tree power-of-two
coefficients, preserving all six primitive advantage arguments. -/
theorem sharp_reduction_bound_le_complete (merkle encoding firstChain secondChain ud pre : ℝ≥0∞) :
    merkle + encoding + firstChain + secondChain +
        (((2 ^ h) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) * pre +
        (((2 ^ h) * v * (2 ^ w - 1) ^ 2 : ℕ) : ℝ≥0∞) * ud ≤
      GXMSS.Unforgeability.reductionBound h w v merkle encoding firstChain secondChain ud pre := by
  unfold GXMSS.Unforgeability.reductionBound
  have hstep : 2 ^ w - 1 ≤ 2 ^ w := Nat.sub_le _ _
  have hpre : (((2 ^ h) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) ≤
      (((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.mul_le_mul_left ((2 ^ h) * v) hstep
  have hud : (((2 ^ h) * v * (2 ^ w - 1) ^ 2 : ℕ) : ℝ≥0∞) ≤
      (((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) * ((2 ^ w : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul]
    exact_mod_cast (show (2 ^ h) * v * (2 ^ w - 1) ^ 2 ≤ (2 ^ h) * v * 2 ^ w * 2 ^ w by
      calc
        _ ≤ (2 ^ h) * v * (2 ^ w) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep 2)
        _ = _ := by ring)
  calc
    _ ≤ merkle + encoding + firstChain + secondChain +
        (((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) * pre +
        ((((2 ^ h) * v * 2 ^ w : ℕ) : ℝ≥0∞) * ((2 ^ w : ℕ) : ℝ≥0∞)) * ud := by
      gcongr
    _ = _ := by
      push_cast
      ring

/-- The global PRE experiment retains the complete full-range interval law, including total
fallback successes after unsuccessful extraction. -/
theorem chainPREExperiment_full_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_PRE_Experiment (Security.chainPreimageReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) hv hw adv) =ᵈ
      SM_DT_PRE_Experiment (GXMSS.Interval.Reductions.Chain.chainPreimageReduction
        hash enc K (GXMSS.IntervalMerkle.Interval.full h) hv hw (adversaryToOrdinary adv)) := by
  apply (chainPREExperiment_single hash enc K J hv hw adv).trans
  exact EvalDistEq.of_evalDist_eq
    (GXMSS.Interval.Unforgeability.chainPreimageExperiment_full hash enc K hv hw
      (adversaryToOrdinary adv)).symm

/-- Each global UD world retains the entire full-range interval Boolean law. -/
theorem chainUDExperiment_full_single [SampleableType H] [SampleableType R]
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
        hash enc K (GXMSS.IntervalMerkle.Interval.full h) hv hw (adversaryToOrdinary adv)) := by
  apply (chainUDExperiment_single hash enc K J hv hw adv world).trans
  exact EvalDistEq.of_evalDist_eq
    (GXMSS.Interval.Unforgeability.chainUndetectabilityExperiment_full hash enc K hv hw
      (adversaryToOrdinary adv) world).symm

/-- The depth-one global bound has exactly the displayed complete-tree sharp right-hand side,
with all six historical named reductions and the same adaptive source adversary. -/
theorem strongUnforgeabilityBound_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    strongUnforgeabilityBound (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      qs hv hw adv =
      SM_DT_TCR_Advantage (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv
        (adversaryToOrdinary adv)) +
      TargetCollisionResistance.advantage (GXMSS.Reductions.encodingTargetCollisionReduction
        hash enc qs K (adversaryToOrdinary adv)) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K
        (adversaryToOrdinary adv)) +
      SM_DT_TCR_Advantage (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K
        (adversaryToOrdinary adv)) +
      (((2 ^ h) * v * (2 ^ w - 1) : ℕ) : ℝ≥0∞) *
        SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw
          (adversaryToOrdinary adv)) +
      (((2 ^ h) * v * (2 ^ w - 1) ^ 2 : ℕ) : ℝ≥0∞) *
        SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw
          (adversaryToOrdinary adv)) := by
  unfold strongUnforgeabilityBound
  rw [merkleTargetCollisionAdvantage_single hash enc K J hv adv,
    EncodingTransport.historical_reduction_advantage_eq hash enc qs K J adv hqueries,
    sameMessageChainTargetCollisionAdvantage_single hash enc K J adv,
    chainCutTargetCollisionAdvantage_single hash enc K J adv,
    chainPREAdvantage_single hash enc K J hv hw adv,
    chainUDAdvantage_single hash enc K J hv hw adv]
  simp only [chainCount_single, singleShape]
  push_cast
  ring

/-- The complete displayed global right-hand side is the retained sharp full-range interval
bound, by actual named experiment transports. -/
theorem strongUnforgeabilityBound_eq_interval_full [SampleableType H] [SampleableType R]
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
        (GXMSS.IntervalMerkle.Interval.full h) hv hw (adversaryToOrdinary adv) := by
  rw [GXMSS.Interval.Unforgeability.strongUnforgeabilityBound_full]
  exact strongUnforgeabilityBound_single hash enc K J qs hv hw adv hqueries

/-- Relaxing only the sharp coefficients yields the unchanged complete-tree bound on the
same six actual named reduction advantages. -/
theorem strongUnforgeabilityBound_single_le_complete [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J qs : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    strongUnforgeabilityBound (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      qs hv hw adv ≤
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
          (adversaryToOrdinary adv))) := by
  rw [strongUnforgeabilityBound_single hash enc K J qs hv hw adv hqueries]
  exact sharp_reduction_bound_le_complete _ _ _ _ _ _

/-- Native depth-one strong unforgeability retains the historical complete-tree relaxed bound.
The fibrewise nonmaximum-output premise and signing-query bound are unchanged. -/
theorem strong_unforgeability_relaxed_complete [SampleableType H] [SampleableType R]
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
  (strong_unforgeability_reduction_bound (liftHash hash) (familyOfEncoding enc)
    (RetrySampling.iid K J) qs hv hw hnonmax adv hqueries).trans
      (strongUnforgeabilityBound_single_le_complete hash enc K J qs hv hw adv hqueries)

end GXMSS.Hypertree.SingleLayer
