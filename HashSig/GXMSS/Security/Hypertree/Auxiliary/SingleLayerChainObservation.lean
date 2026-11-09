/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainInvariant
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainMass
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainContinuation
import all HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Reductions.ChainPreimage

/-!
# Depth-one spliced chain observations

The private retry ledger and the returned signature history give the same reference word at
depth one. Current endpoint, opening and cut observations therefore retain the complete ordinary
chain game, including unused and failed-consumed epochs.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash

variable {PP T X H M R Coins : Type} {h w v : ℕ}

/-- Callback coherence and first-request recording identify every private depth-one reference
with the actual successful encoder equation in its returned signature history. -/
theorem referenceResult_bottom_eq_history
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (pp : PP)
    (sample : ProbComp Coins)
    (attempt : Epoch (singleShape h w v) → M → Coins →
      IncomparableEncoding.IndexedResult R v (2 ^ w))
    (signer : Epoch (singleShape h w v) → M → Coins → Option (Signature R H (singleShape h w v)))
    (hcallback : ∀ ep msg coins, (attempt ep msg coins).output =
      (signer ep msg coins).bind fun sig =>
        (enc.value pp msg sig.bottom.randomizer (epochEquiv ep)).map
          (fun word => (word, sig.bottom.randomizer)))
    (metadata : Security.ChainContinuation.Metadata R H (singleShape h w v))
    (state : Security.NativeState M H R (singleShape h w v))
    (hmatch : Security.AttemptsMatchHistory sample attempt signer state)
    (hcomplete : HistoryHasAttempt state)
    (hnodup : (state.2.map Security.BottomAttempt.epoch).Nodup)
    (ep : Epoch (singleShape h w v)) :
    Security.referenceResult metadata state (bottomPosition _ ep) =
      (state.1 ep).bind fun entry => entry.2.bind fun sig =>
        (enc.value pp entry.1 sig.bottom.randomizer (epochEquiv ep)).map
          (fun word => (word, sig.bottom.randomizer)) := by
  cases hhistory : state.1 ep with
  | none =>
    have hf : ((Security.bottomLedger (H := H) state.2).find?
        fun entry => decide (entry.position = bottomPosition _ ep)) = none := by
      apply List.find?_eq_none.mpr
      intro record hrecord
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hrecord
      intro hdecide
      have hposition := of_decide_eq_true hdecide
      have hepoch : entry.epoch = ep := positionAt_bottom_injective _ hposition
      obtain ⟨coins, _, _, hsame⟩ := hmatch entry hentry
      rw [hepoch, hhistory] at hsame
      contradiction
    rw [Security.referenceResult, dite_eq_left (by rfl), hf]
    rfl
  | some record =>
    obtain ⟨entry, hentry, hepoch, _⟩ := hcomplete ep record.1 record.2 hhistory
    have href := Security.referenceResult_bottom_of_mem metadata state hnodup entry hentry
    rw [hepoch] at href
    rw [href, Option.bind_some]
    obtain ⟨coins, _, hresult, hsame⟩ := hmatch entry hentry
    rw [hepoch, hhistory] at hsame
    have hpair := Option.some.inj hsame
    have hmessage : record.1 = entry.message := congrArg Prod.fst hpair
    have hsign : record.2 = signer ep entry.message coins := congrArg Prod.snd hpair
    rw [hresult, hepoch, hcallback, hmessage, hsign]

/-- The depth-one spliced callback retains exactly its successful encoding word and randomizer. -/
private theorem spliceSign_result_eq_history [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (ep : Epoch (singleShape h w v)) (msg : M) (coins : (RetryPlan.iid R K).Coins) :
    (Security.ChainContinuation.bottomResult (familyOfEncoding (H := H) enc) (RetryPlan.iid R K)
      pp ep msg coins).output =
      (Security.ChainContinuation.spliceSign (liftHash hash) (familyOfEncoding (H := H) enc)
        (RetrySampling.iid K J) pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins
          ep msg coins).bind fun sig =>
        (enc.value pp msg sig.bottom.randomizer (epochEquiv ep)).map
          (fun word => (word, sig.bottom.randomizer)) := by
  have hbind : (Security.ChainContinuation.spliceSign (liftHash hash)
        (familyOfEncoding (H := H) enc)
        (RetrySampling.iid K J) pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins
          ep msg coins).bind (fun sig =>
        (enc.value pp msg sig.bottom.randomizer (epochEquiv ep)).map
          (fun word => (word, sig.bottom.randomizer))) =
      (Option.map signatureEquiv (Security.ChainContinuation.spliceSign (liftHash hash)
        (familyOfEncoding (H := H) enc) (RetrySampling.iid K J) pp splice.1 splice.2.1
          splice.2.2.val
          answer starts upperCoins ep msg coins)).bind fun sig =>
        (enc.value pp msg sig.randomizer (epochEquiv ep)).map
          (fun word => (word, sig.randomizer)) := by
    cases Security.ChainContinuation.spliceSign (liftHash hash) (familyOfEncoding (H := H) enc)
      (RetrySampling.iid K J) pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins
        ep msg coins <;> rfl
  rw [hbind, spliceSign_iid_single, bottomResult_iid_single]
  cases hword : ((RetryPlan.iid R K).run enc pp msg (epochEquiv ep) coins).output with
  | none => rfl
  | some wr =>
    simp only [Option.map_some, Option.bind_some]
    change some wr = (enc.value pp msg wr.2 (epochEquiv ep)).map (fun word => (word, wr.2))
    rw [(RetryPlan.iid R K).value_eq_some_of_run_output_eq_some enc pp msg
      (epochEquiv ep) coins hword]
    rfl

/-- Observe current spliced raw data through the ordinary complete-tree representation. -/
@[expose] def currentSpliceObservation (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (starts ends : OTSPosition (singleShape h w v) → Fin v → H)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)))
    (state : Security.NativeState M H R (singleShape h w v)) :
    GXMSS.Reductions.Result PP H M R h v :=
  ⟨⟨hash.merkleRoot pp (startsEquiv ends), pp⟩, ⟨pp, startsEquiv starts, startsEquiv ends⟩,
    forgeryObservation forgery, historyObservation state.1⟩

/-- The private reference of a reachable depth-one splice is its returned history's exact
successful encoder word, with unused and exhausted records represented by `none`. -/
theorem referenceResult_bottom_splice_single [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (state : Security.NativeState M H R (singleShape h w v))
    (hinv : SpliceStateInvariant (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins state)
    (ep : Epoch (singleShape h w v)) :
    Security.referenceResult (Security.ChainContinuation.prepare (liftHash hash)
      (familyOfEncoding enc) (RetryPlan.iid R J) pp
      (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1 splice.2.1
        splice.2.2.val answer starts) upperCoins) state (bottomPosition _ ep) =
      (state.1 ep).bind fun entry => entry.2.bind fun sig =>
        (enc.value pp entry.1 sig.bottom.randomizer (epochEquiv ep)).map
          (fun word => (word, sig.bottom.randomizer)) :=
  referenceResult_bottom_eq_history enc pp _ _ _
    (spliceSign_result_eq_history hash enc K J pp splice answer starts upperCoins)
    _ state hinv.1 hinv.2.1 hinv.2.2 ep

/-- Every successful returned splice signature has its actual encoder word, current prefix
values and complete authentication path. The sampled attempt and full signature use one coin. -/
theorem successful_splice_history_component [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (state : Security.NativeState M H R (singleShape h w v))
    (hinv : SpliceStateInvariant (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins state)
    (ep : Epoch (singleShape h w v)) (msg : M) (sig : Signature R H (singleShape h w v))
    (hrecord : state.1 ep = some (msg, some sig)) :
    ∃ word, enc.value pp msg sig.bottom.randomizer (epochEquiv ep) = some word ∧
      sig.bottom = Security.ChainContinuation.component
        (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
          (RetryPlan.iid R J) pp (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp
            splice.1 splice.2.1 splice.2.2.val answer starts) upperCoins)
        (Security.ChainContinuation.splicePrefixes (liftHash hash) pp splice.1 splice.2.1
          splice.2.2.val answer starts) (bottomPosition _ ep) (word, sig.bottom.randomizer) := by
  obtain ⟨entry, hentry, hepoch, hmessage⟩ := hinv.2.1 ep msg (some sig) hrecord
  obtain ⟨coins, _, _, hsame⟩ := hinv.1 entry hentry
  rw [hepoch, hmessage, hrecord] at hsame
  have hsigned : Security.ChainContinuation.spliceSign (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins
        ep msg coins = some sig := (congrArg Prod.snd (Option.some.inj hsame)).symm
  have hsig := spliceSign_iid_single hash enc K J pp splice answer starts upperCoins ep msg coins
  rw [hsigned] at hsig
  cases hword : ((RetryPlan.iid R K).run enc pp msg (epochEquiv ep) coins).output with
  | none => simp [hword] at hsig
  | some wr =>
    have heq := Option.some.inj (by simpa only [hword, Option.map_some] using hsig)
    have hcomponent : sig.bottom = Security.ChainContinuation.component
        (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
          (RetryPlan.iid R J) pp (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp
            splice.1 splice.2.1 splice.2.2.val answer starts) upperCoins)
        (Security.ChainContinuation.splicePrefixes (liftHash hash) pp splice.1 splice.2.1
          splice.2.2.val answer starts) (bottomPosition _ ep) wr := by
      calc
        sig.bottom = signatureEquiv sig := rfl
        _ = _ := heq
        _ = _ := (spliceComponent_single hash enc (RetryPlan.iid R J) pp splice answer starts
          upperCoins ep wr).symm
    have hr : sig.bottom.randomizer = wr.2 := congrArg GXMSS.Signature.randomizer hcomponent
    refine ⟨wr.1, ?_, ?_⟩
    · simpa only [hr] using (RetryPlan.iid R K).value_eq_some_of_run_output_eq_some enc
        pp msg (epochEquiv ep) coins hword
    · simpa only [hr, Prod.eta] using hcomponent

/-- A current full opening in the ordinary Game 1 identifies every forged chain's final value
with its current spliced endpoint, without an honest-key or source-support assumption. -/
theorem currentSplice_gameOne_endpoint [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (pp : PP)
    (starts ends : OTSPosition (singleShape h w v) → Fin v → H)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)))
    (state : Security.NativeState M H R (singleShape h w v))
    (word : Codeword v (2 ^ w))
    (hword : enc.value pp forgery.2.1 forgery.2.2.bottom.randomizer
      (epochEquiv forgery.1) = some word)
    (hgame : GXMSS.Reductions.gameOneObservation hash enc K
      (currentSpliceObservation hash pp starts ends forgery state) = true) (i : Fin v) :
    hash.chain pp (epochEquiv forgery.1) i (word i) (2 ^ w - 1 - (word i).val)
        (forgery.2.2.bottom.ots i) = ends (bottomPosition _ forgery.1) i := by
  simpa only [currentSpliceObservation, forgeryObservation, signatureEquiv_apply,
    startsEquiv_apply, bottomPosition_eq] using
    (GXMSS.Reductions.gameOneObservation_endpoint_eq_forged hash enc K
      (currentSpliceObservation hash pp starts ends forgery state) word hword hgame i).symm

end GXMSS.Hypertree.SingleLayer
