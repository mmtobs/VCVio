/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutAlgebra
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutAlgebra
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainContinuation
import all HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-! # Selected chain observations at successful depth-one history records -/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash
open GXMSS.Hypertree.Unforgeability GXMSS.Security

variable {PP T X H M R : Type} {h w v : ℕ}

/-- A successful first-request signature reads its honest digit from the same spliced prefix
as the selected response. Current global and ordinary selected-chain observations therefore agree.
-/
theorem selectedCutObservation_successful_splice_single
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
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
    (message : M) (signature : Signature R H (singleShape h w v))
    (hrecord : state.1 forgery.1 = some (message, some signature)) :
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
            currentSpliceObservation hash pp starts ends forgery state) := by
  rcases forgery with ⟨ep, msg, sig⟩
  let ends := Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
    splice.2.1 splice.2.2.val answer starts
  let metadata := Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
    (RetryPlan.iid R J) pp ends upperCoins
  let prefixes := Security.ChainContinuation.splicePrefixes (liftHash hash) pp splice.1
    splice.2.1 splice.2.2.val answer starts
  let out := currentSpliceObservation hash pp starts ends (ep, msg, sig) state
  obtain ⟨honest, hhonest, hcomponent⟩ := successful_splice_history_component hash enc K J
    pp splice answer starts upperCoins state hinv ep message signature hrecord
  have hsource : GXMSS.Reductions.forgedEpochSource out =
      .successful message signature.bottom := by
    simp only [out, currentSpliceObservation, GXMSS.Reductions.forgedEpochSource,
      historyObservation, forgeryObservation, Equiv.symm_apply_apply, hrecord,
      Option.map_some, signatureEquiv_apply]
  change Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc) pp selector
    (prefixes selector.1 selector.2.1 (selector.2.2.val + 1)) ends metadata
    (Security.ChainContinuation.canonicalReferences metadata prefixes) (ep, msg, sig) state =
      GXMSS.Reductions.jointChainObservation hash enc K (chainPositionEquiv selector, out)
  unfold Security.selectedCutObservation
  rw [decodeCurrent_single hash enc pp ends
    (Security.ChainContinuation.canonicalReferences metadata prefixes) (ep, msg, sig)]
  cases hf : enc.value pp msg sig.bottom.randomizer (epochEquiv ep) with
  | none =>
    change false = GXMSS.Reductions.jointChainObservation hash enc K
      (chainPositionEquiv selector, out)
    have hfo : enc.value out.pk.seed out.forgery.2.1 out.forgery.2.2.randomizer
        out.forgery.1 = none := hf
    have hho : enc.value out.pk.seed message signature.bottom.randomizer
        out.forgery.1 = some honest := hhonest
    simp only [GXMSS.Reductions.jointChainObservation, hsource,
      GXMSS.Reductions.gameFiveObservation, hho, hfo, Bool.and_false]
  | some word =>
    let candidate : ComponentCandidate M R H (singleShape h w v) :=
      ⟨bottomPosition _ ep, bottomMessage ep msg, sig.bottom⟩
    change (Security.cutValidityGuard (liftHash hash) (familyOfEncoding enc) pp ends metadata
      (ep, msg, sig) state candidate word &&
      (if Security.chooseCurrentChain candidate word
          (Security.referenceResult metadata state candidate.position) = some selector then
        decide ((word selector.2.1).val < selector.2.2.val + 1 ∧
          (Security.ChainContinuation.chainFamily (liftHash hash) pp).chain selector.1
            selector.2.1 (word selector.2.1).val
            (selector.2.2.val + 1 - (word selector.2.1).val) (sig.bottom.ots selector.2.1) =
              prefixes selector.1 selector.2.1 (selector.2.2.val + 1)) else false)) = _
    rw [cutValidityGuard_current_single hash enc K J pp starts ends upperCoins
      (ep, msg, sig) state word hf]
    have href := referenceResult_bottom_splice_single hash enc K J pp splice answer starts
      upperCoins state hinv ep
    rw [hrecord, Option.bind_some, Option.bind_some, hhonest, Option.map_some] at href
    rw [href]
    cases hi : findSmallerCoordinate honest word with
    | none =>
      rw [chooseCurrentChain_no_smaller candidate word honest signature.bottom.randomizer hi]
      simp only [reduceCtorEq, ↓reduceIte, Bool.and_false]
      have hfo : enc.value out.pk.seed out.forgery.2.1 out.forgery.2.2.randomizer
          out.forgery.1 = some word := hf
      have hho : enc.value out.pk.seed message signature.bottom.randomizer
          out.forgery.1 = some honest := hhonest
      simp only [GXMSS.Reductions.jointChainObservation, hsource,
        GXMSS.Reductions.gameFiveObservation, hho, hfo, hi, Bool.and_false]
    | some i =>
      have hsel : Security.chooseCurrentChain candidate word
          (some (honest, signature.bottom.randomizer)) = some selector ↔
          (chainPositionEquiv selector).1 = epochEquiv ep ∧
          (chainPositionEquiv selector).2.1 = i ∧
          (chainPositionEquiv selector).2.2.val + 1 = (honest i).val := by
        rw [chooseCurrentChain_success_iff candidate word honest signature.bottom.randomizer
          i selector hi]
        exact and_congr (bottomPosition_selector_iff ep selector) Iff.rfl
      have hold := jointChainObservation_success_iff hash enc K out
        (chainPositionEquiv selector) message signature.bottom honest word i hsource hhonest hf hi
      by_cases hs : Security.chooseCurrentChain candidate word
          (some (honest, signature.bottom.randomizer)) = some selector
      · have hc := (chooseCurrentChain_success_iff candidate word honest
          signature.bottom.randomizer i selector hi).mp hs
        have hlt : (word selector.2.1).val < selector.2.2.val + 1 := by
          rw [hc.2.1, hc.2.2]
          exact findSmallerCoordinate_sound honest word hi
        have hprefix : signature.bottom.ots i =
            prefixes (bottomPosition _ ep) i (honest i).val :=
          congrArg (fun signature : GXMSS.Signature R H h v => signature.ots i) hcomponent
        have hresponse : prefixes (topTree (singleShape h w v), epochEquiv ep) i
            (honest i).val = signature.bottom.ots i := by
          simpa only [bottomPosition_eq] using hprefix.symm
        apply Bool.eq_iff_iff.mpr
        rw [hold]
        simp only [hs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hone, _, hchain⟩
          refine ⟨hone, ?_, hsel.mp hs⟩
          simpa only [Security.ChainContinuation.chainFamily, componentHash_liftHash,
            candidate, ← hc.1, hc.2.1, hc.2.2, bottomPosition_eq, hresponse,
            out, currentSpliceObservation, forgeryObservation, signatureEquiv_apply] using hchain
        · rintro ⟨hone, hchain, _⟩
          refine ⟨hone, hlt, ?_⟩
          simpa only [Security.ChainContinuation.chainFamily, componentHash_liftHash,
            candidate, ← hc.1, hc.2.1, hc.2.2, bottomPosition_eq, hresponse,
            out, currentSpliceObservation, forgeryObservation, signatureEquiv_apply] using hchain
      · have hnot : ¬ GXMSS.Reductions.jointChainObservation hash enc K
            (chainPositionEquiv selector, out) = true := by
          intro hwin
          exact hs (hsel.mpr (hold.mp hwin).2.2)
        simpa only [hs, ↓reduceIte, Bool.and_false] using (Bool.eq_false_iff.mpr hnot).symm

end GXMSS.Hypertree.SingleLayer
