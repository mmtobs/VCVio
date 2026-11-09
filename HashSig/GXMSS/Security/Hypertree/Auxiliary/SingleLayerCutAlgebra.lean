/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainObservation
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainInvariant
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainObservation
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses
import all HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.SourceGames

/-!
# Depth-one selected-cut algebra

Current endpoint guards, first-smaller scans and complete ordinary chain observations share
the same selected coordinates and positive cut positions.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash
open GXMSS.Hypertree.Unforgeability GXMSS.Security

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The depth-one current decoder always inspects the bottom component. -/
theorem decodeCurrent_single [DecidableEq H] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (pp : PP)
    (ends : OTSPosition (singleShape h w v) → Fin v → H)
    (references : UpperPosition (singleShape h w v) → Option (GXMSS.Signature R H h v))
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))) :
    Security.decodeCurrent (liftHash hash) (familyOfEncoding enc) pp ends references forgery =
      (do
        let word ← enc.value pp forgery.2.1 forgery.2.2.bottom.randomizer (epochEquiv forgery.1)
        pure (⟨bottomPosition _ forgery.1, bottomMessage forgery.1 forgery.2.1,
          forgery.2.2.bottom⟩, word)) := by
  rcases forgery with ⟨ep, msg, sig⟩
  change (do
    let word ← enc.value pp (messageEquiv (bottomPosition _ ep)
      (bottomMessage ep msg)) sig.bottom.randomizer
        (bottomPosition (singleShape h w v) ep).2
    pure ((⟨bottomPosition _ ep, bottomMessage ep msg,
      sig.bottom⟩ : ComponentCandidate M R H (singleShape h w v)), word)) = _
  rw [messageEquiv_bottomMessage]
  rw [show (bottomPosition (singleShape h w v) ep).2 = epochEquiv ep from
    otsEquiv_bottomPosition ep]

/-- The prepared current opening guard is the ordinary first chain-game observation. -/
theorem cutValidityGuard_current_single [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (starts ends : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)))
    (state : Security.NativeState M H R (singleShape h w v)) (word : Codeword v (2 ^ w))
    (hword : enc.value pp forgery.2.1 forgery.2.2.bottom.randomizer (epochEquiv forgery.1) =
      some word) :
    Security.cutValidityGuard (liftHash hash) (familyOfEncoding enc) pp ends
      (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
        (RetryPlan.iid R J) pp ends upperCoins) forgery state
      ⟨bottomPosition _ forgery.1, bottomMessage forgery.1 forgery.2.1, forgery.2.2.bottom⟩ word =
        GXMSS.Reductions.gameOneObservation hash enc K
          (currentSpliceObservation hash pp starts ends forgery state) := by
  let out : Security.Result PP H M R (RetryPlan.iid R J).Coins (singleShape h w v) :=
    ⟨⟨componentRoot (liftHash hash) pp ends (topTree _), pp⟩,
      ⟨pp, starts, ends, upperCoins⟩, forgery, state.1,
      fun p => (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
        (RetryPlan.iid R J) pp ends upperCoins).internalResults p, state.2⟩
  have hg := cutValidityGuard_single hash enc K J out rfl rfl word hword
  dsimp only [RetrySampling.iid] at hg
  simpa only [out, enrichedSourceObservation, currentSpliceObservation, componentRoot_eq,
    secretKeyEquiv, Equiv.coe_fn_mk, ← startsEquiv_apply, Prod.eta] using hg

private theorem gameThree_eq_gameOne_of_smaller [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (out : GXMSS.Reductions.Result PP H M R h v) (msg : M)
    (sig : GXMSS.Signature R H h v) (honest forged : Codeword v (2 ^ w)) (i : Fin v)
    (hsource : GXMSS.Reductions.forgedEpochSource out = .successful msg sig)
    (hhonest : enc.value out.pk.seed msg sig.randomizer out.forgery.1 = some honest)
    (hforged : enc.value out.pk.seed out.forgery.2.1 out.forgery.2.2.randomizer out.forgery.1 =
      some forged)
    (hsmall : findSmallerCoordinate honest forged = some i) :
    GXMSS.Reductions.gameThreeObservation hash enc K out =
      GXMSS.Reductions.gameOneObservation hash enc K out := by
  have hlt := findSmallerCoordinate_sound honest forged hsmall
  have hne : honest ≠ forged := by
    intro heq
    subst forged
    exact (lt_irrefl _ hlt)
  have hpair : (msg, sig.randomizer) ≠ (out.forgery.2.1, out.forgery.2.2.randomizer) := by
    intro hp
    have hm := congrArg Prod.fst hp
    have hr := congrArg Prod.snd hp
    dsimp only at hm hr
    rw [hm, hr, hforged] at hhonest
    exact hne (Option.some.inj hhonest).symm
  simp [GXMSS.Reductions.gameThreeObservation, GXMSS.Reductions.gameTwoObservation,
    hsource, hhonest, hforged, hne, hpair]

private theorem chooseCurrentChain_success_iff
    (candidate : ComponentCandidate M R H (singleShape h w v))
    (word honest : Codeword v (2 ^ w)) (r : R) (i : Fin v)
    (selector : ChainPosition (singleShape h w v))
    (hi : findSmallerCoordinate honest word = some i) :
    Security.chooseCurrentChain candidate word (some (honest, r)) = some selector ↔
      candidate.position = selector.1 ∧ selector.2.1 = i ∧
        selector.2.2.val + 1 = (honest i).val := by
  have hlt := findSmallerCoordinate_sound honest word hi
  unfold Security.chooseCurrentChain
  dsimp only
  split
  · rename_i hn
    simp [hi] at hn
  · rename_i j hj
    have hji : j = i := Option.some.inj (hj.symm.trans hi)
    subst j
    simp only [Option.some.injEq]
    constructor
    · intro heq
      have hc := congrArg (fun p : ChainPosition (singleShape h w v) => p.2.1) heq
      have hn := congrArg (fun p : ChainPosition (singleShape h w v) => p.2.2.val) heq
      refine ⟨congrArg Prod.fst heq, hc.symm, ?_⟩
      dsimp only at hn
      omega
    · rintro ⟨hp, hc, hcut⟩
      apply Prod.ext hp
      apply Prod.ext hc.symm
      apply Fin.ext
      dsimp only
      omega

private theorem chooseCurrentChain_none_iff
    (candidate : ComponentCandidate M R H (singleShape h w v))
    (word : Codeword v (2 ^ w)) (i : Fin v)
    (selector : ChainPosition (singleShape h w v))
    (hi : GXMSS.Reductions.findNonMaximumCoordinate word = some i) :
    Security.chooseCurrentChain candidate word none = some selector ↔
      candidate.position = selector.1 ∧ selector.2.1 = i ∧
        selector.2.2.val + 1 = 2 ^ w - 1 := by
  have hlt := GXMSS.Reductions.findNonMaximumCoordinate_sound word hi
  unfold Security.chooseCurrentChain
  dsimp only
  split
  · rename_i hn
    simp [hi] at hn
  · rename_i j hj
    have hji : j = i := Option.some.inj (hj.symm.trans hi)
    subst j
    simp only [Option.some.injEq]
    constructor
    · intro heq
      have hc := congrArg (fun p : ChainPosition (singleShape h w v) => p.2.1) heq
      have hn := congrArg (fun p : ChainPosition (singleShape h w v) => p.2.2.val) heq
      refine ⟨congrArg Prod.fst heq, hc.symm, ?_⟩
      dsimp only at hn
      omega
    · rintro ⟨hp, hc, hcut⟩
      apply Prod.ext hp
      apply Prod.ext hc.symm
      apply Fin.ext
      dsimp only
      omega

private theorem jointChainObservation_success_iff [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (out : GXMSS.Reductions.Result PP H M R h v) (guess : GXMSS.Reductions.Guess h w v)
    (msg : M) (sig : GXMSS.Signature R H h v)
    (honest forged : Codeword v (2 ^ w)) (i : Fin v)
    (hsource : GXMSS.Reductions.forgedEpochSource out = .successful msg sig)
    (hhonest : enc.value out.pk.seed msg sig.randomizer out.forgery.1 = some honest)
    (hforged : enc.value out.pk.seed out.forgery.2.1 out.forgery.2.2.randomizer out.forgery.1 =
      some forged) (hsmall : findSmallerCoordinate honest forged = some i) :
    GXMSS.Reductions.jointChainObservation hash enc K (guess, out) = true ↔
      GXMSS.Reductions.gameOneObservation hash enc K out = true ∧
      hash.chain out.pk.seed out.forgery.1 i (forged i)
        ((honest i).val - (forged i).val) (out.forgery.2.2.ots i) = sig.ots i ∧
      (guess.1 = out.forgery.1 ∧ guess.2.1 = i ∧ guess.2.2.val + 1 = (honest i).val) := by
  rcases out with ⟨pk, sk, ⟨ep, message, signature⟩, history⟩
  rcases guess with ⟨ge, gi, gp⟩
  have hthree := gameThree_eq_gameOne_of_smaller hash enc K
    ⟨pk, sk, (ep, message, signature), history⟩ msg sig honest forged i
    hsource hhonest hforged hsmall
  simp only [GXMSS.Reductions.jointChainObservation, hsource,
    GXMSS.Reductions.gameFiveObservation, GXMSS.Reductions.gameFourObservation, hthree,
    GXMSS.Reductions.designatedCutHolds, hhonest, hforged, hsmall,
    GXMSS.Reductions.guessedEpoch, GXMSS.Reductions.guessedChain,
    GXMSS.Reductions.guessedPosition, Bool.and_eq_true, decide_eq_true_eq]
  rw [and_assoc]
  constructor
  · rintro ⟨hone, hchain, hguess⟩
    exact ⟨hone, hchain, of_decide_eq_true hguess⟩
  · rintro ⟨hone, hchain, hguess⟩
    exact ⟨hone, hchain, decide_eq_true hguess⟩

private theorem jointChainObservation_no_signature [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pp : PP) (starts ends : OTSPosition (singleShape h w v) → Fin v → H)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)))
    (state : Security.NativeState M H R (singleShape h w v))
    (hrecord : (state.1 forgery.1).bind Prod.snd = none)
    (guess : GXMSS.Reductions.Guess h w v) :
    let out := currentSpliceObservation hash pp starts ends forgery state
    GXMSS.Reductions.jointChainObservation hash enc K (guess, out) =
      (GXMSS.Reductions.gameOneObservation hash enc K out &&
        match enc.value pp forgery.2.1 forgery.2.2.bottom.randomizer (epochEquiv forgery.1) with
        | none => false
        | some word => match GXMSS.Reductions.findNonMaximumCoordinate word with
          | none => false
          | some i => decide (guess.1 = epochEquiv forgery.1 ∧ guess.2.1 = i ∧
              guess.2.2.val + 1 = 2 ^ w - 1)) := by
  rcases forgery with ⟨ep, message, signature⟩
  rcases state with ⟨history, attempts⟩
  rcases guess with ⟨ge, gi, gp⟩
  cases hh : history ep with
  | none =>
    simp only [GXMSS.Reductions.jointChainObservation, GXMSS.Reductions.forgedEpochSource,
      currentSpliceObservation, historyObservation, forgeryObservation,
      GXMSS.Reductions.gameFourObservation, GXMSS.Reductions.gameThreeObservation,
      GXMSS.Reductions.gameTwoObservation, GXMSS.Reductions.designatedCutHolds, hh,
      signatureEquiv_apply, GXMSS.Reductions.guessedEpoch, GXMSS.Reductions.guessedChain,
      GXMSS.Reductions.guessedPosition, Equiv.symm_apply_apply, Option.map_none,
      Bool.and_true]
    rfl
  | some pair =>
    rcases pair with ⟨msg, signature⟩
    cases signature with
    | none =>
      simp only [GXMSS.Reductions.jointChainObservation, GXMSS.Reductions.forgedEpochSource,
        currentSpliceObservation, historyObservation, forgeryObservation,
        GXMSS.Reductions.gameFourObservation, GXMSS.Reductions.gameThreeObservation,
        GXMSS.Reductions.gameTwoObservation, GXMSS.Reductions.designatedCutHolds, hh,
        signatureEquiv_apply, GXMSS.Reductions.guessedEpoch, GXMSS.Reductions.guessedChain,
        GXMSS.Reductions.guessedPosition, Equiv.symm_apply_apply, Option.map_none,
      Option.map_some, Bool.and_true]
      rfl
    | some sig => simp [hh] at hrecord

private theorem chooseCurrentChain_no_smaller
    (candidate : ComponentCandidate M R H (singleShape h w v))
    (word honest : Codeword v (2 ^ w)) (r : R)
    (hi : findSmallerCoordinate honest word = none) :
    Security.chooseCurrentChain candidate word (some (honest, r)) = none := by
  unfold Security.chooseCurrentChain
  dsimp only
  split
  · rfl
  · rename_i j hj
    simp [hi] at hj

private theorem chooseCurrentChain_no_nonmaximum
    (candidate : ComponentCandidate M R H (singleShape h w v))
    (word : Codeword v (2 ^ w))
    (hi : GXMSS.Reductions.findNonMaximumCoordinate word = none) :
    Security.chooseCurrentChain candidate word none = none := by
  unfold Security.chooseCurrentChain
  dsimp only
  split
  · rfl
  · rename_i j hj
    simp [hi] at hj

private theorem referenceResult_no_signature [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (state : Security.NativeState M H R (singleShape h w v))
    (hinv : SpliceStateInvariant (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins state)
    (ep : Epoch (singleShape h w v)) (hrecord : (state.1 ep).bind Prod.snd = none) :
    Security.referenceResult (Security.ChainContinuation.prepare (liftHash hash)
      (familyOfEncoding enc) (RetryPlan.iid R J) pp
      (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1 splice.2.1
        splice.2.2.val answer starts) upperCoins) state (bottomPosition _ ep) = none := by
  rw [referenceResult_bottom_splice_single hash enc K J pp splice answer starts upperCoins
    state hinv ep]
  cases hh : state.1 ep with
  | none => rfl
  | some pair =>
    rcases pair with ⟨msg, signature⟩
    cases signature with
    | none => rfl
    | some sig => simp [hh] at hrecord

private theorem bottomPosition_selector_iff
    (ep : Epoch (singleShape h w v)) (selector : ChainPosition (singleShape h w v)) :
    bottomPosition _ ep = selector.1 ↔ (chainPositionEquiv selector).1 = epochEquiv ep := by
  change bottomPosition _ ep = selector.1 ↔ otsEquiv selector.1 = epochEquiv ep
  rw [← otsEquiv_bottomPosition ep]
  exact ⟨fun h => congrArg otsEquiv h.symm, fun h => otsEquiv.injective h.symm⟩

end GXMSS.Hypertree.SingleLayer
