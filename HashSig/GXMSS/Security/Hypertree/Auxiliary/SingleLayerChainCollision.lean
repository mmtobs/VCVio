/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames
public import HashSig.GXMSS.Security.Reductions.ChainCutCollision
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames
import all HashSig.GXMSS.Security.Reductions.ChainCutCollision
import all HashSig.GXMSS.Security.Reductions.SameMessageChainCollision
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
import all HashSig.GXMSS.Hypertree.SingleLayer
import all HashSig.GXMSS.Hypertree.Scheme

/-!
# Exact depth-one designated-cut collision experiment

The native reference ledger agrees with the successful first-request history at depth one.
The same designated cut, ordered registered target and total fallback are retained.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash
open GXMSS.Hypertree.Unforgeability GXMSS.Security

variable {PP T X H M R Coins : Type} {h w v : ℕ}

private theorem sourceChainCutWitness_none_of_reference_none [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (out : Security.Result PP H M R Coins (singleShape h w v))
    (hnone : Security.referenceSignatureAt (liftHash hash) out
      (bottomPosition _ out.forgery.1) = none) :
    sourceChainCutWitness? (liftHash hash) (familyOfEncoding enc) out = none := by
  rw [sourceChainCutWitness?, sourceDecoded?_single]
  cases enc.value out.sk.seed out.forgery.2.1 out.forgery.2.2.bottom.randomizer
      (epochEquiv out.forgery.1) with
  | none => rfl
  | some word =>
    change (Security.referenceAt (liftHash hash) out (bottomPosition _ out.forgery.1)).bind _ = none
    cases href : Security.referenceAt (liftHash hash) out (bottomPosition _ out.forgery.1) with
    | none => rfl
    | some entry =>
      change entry.result.bind _ = none
      cases hr : entry.result with
      | none => rfl
      | some wr =>
        simp only [Security.referenceSignatureAt, href, Option.bind_some, hr,
          Option.map_some] at hnone
        cases hnone

private theorem secondChainCandidate_single [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (out : Security.Result PP H M R sampling.internal.Coins (singleShape h w v))
    (hout : out ∈ support (Security.sourceProgram (liftHash hash) (familyOfEncoding enc)
      sampling adv)) (fallback : H) :
    witnessCandidate (chainLedger (liftHash hash) out.sk.seed out.sk.starts)
      (hash.digestInput fallback)
      (sourceChainCutWitness? (liftHash hash) (familyOfEncoding enc) out) =
      GXMSS.Unforgeability.secondChainCandidate hash enc
        ⟨startsEquiv out.sk.starts, startsEquiv out.sk.endpoints, fallback,
          GXMSS.Reductions.endpointTargets hash out.sk.seed (startsEquiv out.sk.starts), fallback⟩
        out.sk.seed (enrichedSourceObservation out) := by
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history, upper, bottom⟩
  change Epoch (singleShape h w v) → Option (M × Option (Signature R H (singleShape h w v)))
    at history
  let out : Security.Result PP H M R sampling.internal.Coins (singleShape h w v) :=
    ⟨pk, sk, (epoch, message, signature), history, upper, bottom⟩
  change out ∈ support (Security.sourceProgram (liftHash hash) (familyOfEncoding enc) sampling adv)
    at hout
  let ep := out.forgery.1
  let p := bottomPosition (singleShape h w v) ep
  have he : p.2 = epochEquiv ep := otsEquiv_bottomPosition ep
  have hp : p.1 = topTree (singleShape h w v) := tree_eq_top _
  rw [chainLedger_single]
  cases href : Security.referenceAt (liftHash hash) out p with
  | none =>
    have hnone : Security.referenceSignatureAt (liftHash hash) out p = none := by
      simp only [Security.referenceSignatureAt, href, Option.bind_none]
    have hh := history_no_success_of_reference_none (liftHash hash) (familyOfEncoding enc)
      sampling adv out hout ep hnone
    rw [sourceChainCutWitness_none_of_reference_none hash enc out hnone, witnessCandidate]
    unfold GXMSS.Unforgeability.secondChainCandidate enrichedSourceObservation
      forgeryObservation historyObservation
    simp only [Equiv.symm_apply_apply, signatureEquiv_apply]
    cases hx : out.history ep with
    | none => simp_all [out, ep]
    | some pair =>
      rcases pair with ⟨msg, answer⟩
      cases answer with
      | none => simp_all [out, ep]
      | some sig =>
        simp only [hx, Option.bind_some] at hh
        cases hh
  | some entry =>
    cases hr : entry.result with
    | none =>
      have hnone : Security.referenceSignatureAt (liftHash hash) out p = none := by
        simp only [Security.referenceSignatureAt, href, Option.bind_some, hr, Option.map_none]
      have hh := history_no_success_of_reference_none (liftHash hash) (familyOfEncoding enc)
        sampling adv out hout ep hnone
      rw [sourceChainCutWitness_none_of_reference_none hash enc out hnone, witnessCandidate]
      unfold GXMSS.Unforgeability.secondChainCandidate enrichedSourceObservation
        forgeryObservation historyObservation
      simp only [Equiv.symm_apply_apply, signatureEquiv_apply]
      cases hx : out.history ep with
      | none => simp_all [out, ep]
      | some pair =>
        rcases pair with ⟨msg, answer⟩
        cases answer with
        | none => simp_all [out, ep]
        | some sig =>
          simp only [hx, Option.bind_some] at hh
          cases hh
    | some wr =>
      have hh := referenceAt_success_history_single (liftHash hash) (familyOfEncoding enc)
        sampling adv out hout ep entry wr href hr
      have hv := Security.referenceAt_value_eq_some (liftHash hash) (familyOfEncoding enc)
        sampling adv out hout p entry href wr.1 wr.2 hr
      have hep := Security.referenceAt_position (liftHash hash) out p entry href
      rw [familyOfEncoding_value] at hv
      have hleaf : entry.position.2 = epochEquiv ep := (congrArg Prod.snd hep).trans he
      rw [hleaf] at hv
      unfold sourceChainCutWitness?
      rw [sourceDecoded?_single]
      cases hf : enc.value out.sk.seed out.forgery.2.1 out.forgery.2.2.bottom.randomizer
          (epochEquiv ep) with
      | none =>
        change (0, hash.digestInput fallback) = _
        unfold GXMSS.Unforgeability.secondChainCandidate enrichedSourceObservation
          forgeryObservation historyObservation
        simp only [Equiv.symm_apply_apply]
        dsimp only [out, ep, p] at hh hv hf ⊢
        rw [hh]
        simp only [Option.map_some, Equiv.apply_symm_apply, componentSignature_eq,
          otsEquiv_bottomPosition, GXMSS.signatureOfWord, signatureEquiv_apply]
        rw [hv, hf]
      | some word =>
        change witnessCandidate _ _ ((Security.referenceAt (liftHash hash) out p).bind _) = _
        rw [href]
        change witnessCandidate _ _ (entry.result.bind _) = _
        rw [hr]
        unfold GXMSS.Unforgeability.secondChainCandidate enrichedSourceObservation
          forgeryObservation historyObservation
        simp only [Equiv.symm_apply_apply]
        dsimp only [out, ep, p] at hh hv hf ⊢
        rw [hh]
        simp only [Option.map_some, Equiv.apply_symm_apply, componentSignature_eq,
          otsEquiv_bottomPosition, GXMSS.signatureOfWord, signatureEquiv_apply]
        rw [hv, hf]
        dsimp only
        let canonical := GXMSS.signatureOfWord hash (secretKeyEquiv _ sk) (epochEquiv epoch) wr
        change witnessCandidate _ _ ((findSmallerCoordinate wr.1 word).bind _) = _
        cases hi : findSmallerCoordinate wr.1 word with
        | none => rfl
        | some i =>
          simp only [Option.bind_some, componentHash_liftHash]
          rw [show (bottomPosition (singleShape h w v) epoch).2 = epochEquiv epoch from
            otsEquiv_bottomPosition epoch]
          change witnessCandidate _ _ ((hash.findChainCut sk.seed (epochEquiv epoch) i
            (word i) (wr.1 i) (2 ^ w - 1) (canonical.ots i) (signature.bottom.ots i)).bind _) = _
          cases hc : hash.findChainCut sk.seed (epochEquiv epoch) i
            (word i) (wr.1 i) (2 ^ w - 1) (canonical.ots i) (signature.bottom.ots i) with
          | none =>
              simp only [canonical, GXMSS.signatureOfWord] at hc
              rw [hc]
              rfl
          | some cut =>
              simp only [canonical, GXMSS.signatureOfWord] at hc
              rw [hc]
              cases cut <;> rfl

private def ordinarySecondChainObservation [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (fallback : H) (out : GXMSS.Reductions.Result PP H M R h v) : Bool :=
  let ledger := GXMSS.Reductions.endpointTargets hash out.sk.seed out.sk.starts
  let state : GXMSS.Reductions.TCRKeyState PP T X H h v :=
    ⟨out.sk.starts, out.sk.endpoints, fallback, ledger, fallback⟩
  GXMSS.Unforgeability.firstChainCandidateWins hash out.sk.seed ledger
    (GXMSS.Unforgeability.secondChainCandidate hash enc state out.sk.seed out)

private theorem ordinarySecondProgram_source_evalDistEq [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Unforgeability.secondChainCoupledProgram hash enc K adv =ᵈ
      (do let fallback ← ($ᵗ H : ProbComp H)
          ordinarySecondChainObservation hash enc fallback <$>
            GXMSS.Reductions.sourceProgram hash enc K adv) := by
  let : MeasurableSpace Bool := ⊤
  apply EvalDistEq.of_evalDist_eq
  unfold GXMSS.Unforgeability.secondChainCoupledProgram
  rw [OracleComp.evalDist_bind_bind_swap]
  apply OracleComp.evalDist_bind_congr_of_support
  intro fallback _
  simp only [GXMSS.Reductions.sourceProgram, GXMSS.keygen, map_bind, bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_congr_of_support
  intro pp _
  apply OracleComp.evalDist_bind_congr_of_support
  intro starts _
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_congr_of_support
  intro out hout
  have hk := GXMSS.Reductions.runWithKeys_support_keys hash enc K adv
    (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 out hout
  simp only [ordinarySecondChainObservation, hk.2, GXMSS.keys]

/-- The actual designated-cut chain reduction preserves the old complete Boolean experiment,
including the total digest fallback after every unsuccessful extraction. -/
theorem chainCutTargetCollisionExperiment_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Experiment (chainCutTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) adv) =ᵈ
      SM_DT_TCR_Experiment (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K
        (adversaryToOrdinary adv)) := by
  rw [chainCutTargetCollisionReduction, chainCollisionReduction_experiment]
  unfold chainCollisionProgram
  rw [GXMSS.Unforgeability.secondChainExperiment_eq_coupled]
  apply EvalDistEq.trans (collisionProgram_source_evalDistEq _ _ _ _ _ _ _)
  apply EvalDistEq.trans _ (ordinarySecondProgram_source_evalDistEq hash enc K
    (adversaryToOrdinary adv)).symm
  apply EvalDistEq.bind_right
  intro fallback
  have hs := (sourceProgram_iid_evalDistEq hash enc K J adv).map
    (ordinarySecondChainObservation hash enc fallback)
  apply EvalDistEq.trans _ hs
  let : MeasurableSpace Bool := ⊤
  apply EvalDistEq.of_evalDist_eq
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply OracleComp.evalDist_bind_congr_of_support
  intro out hout
  unfold sourceCollisionObservation
  dsimp only
  rw [show (liftHash hash).digestInput = hash.digestInput from rfl]
  rw [secondChainCandidate_single hash enc (RetrySampling.iid K J) adv out hout fallback,
    chainLedger_single]
  rfl

/-- Equality of the entire native B2 experiment yields equality of its advantage. -/
theorem chainCutTargetCollisionAdvantage_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Advantage (chainCutTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) adv) =
      SM_DT_TCR_Advantage (GXMSS.Reductions.secondChainTargetCollisionReduction hash enc K
        (adversaryToOrdinary adv)) := by
  exact congrArg (fun measure => measure {true})
    (chainCutTargetCollisionExperiment_single hash enc K J adv).evalDist_eq


end GXMSS.Hypertree.SingleLayer
