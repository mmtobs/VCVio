/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutAlgebra
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutSuccess
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutAlgebra
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainInvariant
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainObservation
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses
import all HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Depth-one selected-cut observations

Current endpoint openings and successful signature prefixes identify the global selected-cut
observation with the complete ordinary joint chain event.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash
open GXMSS.Hypertree.Unforgeability GXMSS.Security

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Unused and failed-consumed depth-one epochs have the exact terminal selected-cut event. -/
theorem selectedCutObservation_no_signature [SampleableType H] [SampleableType R]
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
    (hrecord : (state.1 forgery.1).bind Prod.snd = none)
 :
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
  change Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc) pp selector
    (prefixes selector.1 selector.2.1 (selector.2.2.val + 1)) ends metadata
    (Security.ChainContinuation.canonicalReferences metadata prefixes) (ep, msg, sig) state =
      GXMSS.Reductions.jointChainObservation hash enc K (chainPositionEquiv selector, out)
  rw [jointChainObservation_no_signature hash enc K pp starts ends (ep, msg, sig) state
    hrecord (chainPositionEquiv selector)]
  unfold Security.selectedCutObservation
  rw [decodeCurrent_single hash enc pp ends
    (Security.ChainContinuation.canonicalReferences metadata prefixes) (ep, msg, sig)]
  let candidate : ComponentCandidate M R H (singleShape h w v) :=
    ⟨bottomPosition _ ep, bottomMessage ep msg, sig.bottom⟩
  cases hf : enc.value pp msg sig.bottom.randomizer (epochEquiv ep) with
  | none => simp
  | some word =>
    change (Security.cutValidityGuard (liftHash hash) (familyOfEncoding enc) pp ends metadata
      (ep, msg, sig) state candidate word &&
      (if Security.chooseCurrentChain candidate word
          (Security.referenceResult metadata state candidate.position) = some selector then
        decide ((word selector.2.1).val < selector.2.2.val + 1 ∧
          (Security.ChainContinuation.chainFamily (liftHash hash) pp).chain selector.1 selector.2.1
            (word selector.2.1).val (selector.2.2.val + 1 - (word selector.2.1).val)
            (sig.bottom.ots selector.2.1) = prefixes selector.1 selector.2.1
              (selector.2.2.val + 1)) else false)) = _
    rw [cutValidityGuard_current_single hash enc K J pp starts ends upperCoins
      (ep, msg, sig) state word hf]
    have href := referenceResult_no_signature hash enc K J pp splice answer starts upperCoins
      state hinv ep hrecord
    rw [href]
    cases hi : GXMSS.Reductions.findNonMaximumCoordinate word with
    | none =>
      rw [chooseCurrentChain_no_nonmaximum candidate word hi]
      simp [hi]
    | some i =>
      have hsel : Security.chooseCurrentChain candidate word none = some selector ↔
          (chainPositionEquiv selector).1 = epochEquiv ep ∧
          (chainPositionEquiv selector).2.1 = i ∧
          (chainPositionEquiv selector).2.2.val + 1 = 2 ^ w - 1 := by
        rw [chooseCurrentChain_none_iff candidate word i selector hi]
        exact and_congr (bottomPosition_selector_iff ep selector) Iff.rfl
      simp only [hi]
      by_cases hs : Security.chooseCurrentChain candidate word none = some selector
      · have hcoords := hsel.mp hs
        have hc := (chooseCurrentChain_none_iff candidate word i selector hi).mp hs
        have hlt : (word selector.2.1).val < selector.2.2.val + 1 := by
          rw [hc.2.1, hc.2.2]
          exact GXMSS.Reductions.findNonMaximumCoordinate_sound word hi
        by_cases hone : GXMSS.Reductions.gameOneObservation hash enc K
            (currentSpliceObservation hash pp starts ends (ep, msg, sig) state) = true
        · have he := currentSplice_gameOne_endpoint hash enc K pp starts ends
            (ep, msg, sig) state word hf hone selector.2.1
          have hposition : bottomPosition (singleShape h w v) ep = selector.1 := hc.1
          have hresponse : hash.chain pp (epochEquiv ep) selector.2.1 (word selector.2.1)
              (selector.2.2.val + 1 - (word selector.2.1).val) (sig.bottom.ots selector.2.1) =
              prefixes selector.1 selector.2.1 (selector.2.2.val + 1) := by
            rw [hc.2.2, he]
            rw [hposition]
            rfl
          simp only [hs, ↓reduceIte, hone, Bool.true_and, decide_eq_true hcoords]
          apply decide_eq_true
          exact ⟨hlt, by simpa only [Security.ChainContinuation.chainFamily,
            componentHash_liftHash, bottomPosition_eq, ← hposition] using hresponse⟩
        · have hfalse := Bool.eq_false_iff.mpr hone
          simp only [hs, ↓reduceIte, hfalse, Bool.false_and]
      · have hnot := mt hsel.mpr hs
        simp only [chainPositionEquiv_apply] at hnot
        simp [hs, hnot]

/-- The actual depth-one selected-cut observation equals the complete ordinary joint chain
event. Successful, unused and failed-consumed first-request histories all retain their cases. -/
theorem selectedCutObservation_splice_single [SampleableType H] [SampleableType R]
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
      pp splice.1 splice.2.1 splice.2.2.val answer starts upperCoins state) :
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
  cases hh : state.1 forgery.1 with
  | none =>
    apply selectedCutObservation_no_signature hash enc K J pp selector splice answer starts
      upperCoins forgery state hinv
    rw [hh]
    rfl
  | some pair =>
    rcases pair with ⟨message, signature⟩
    cases signature with
    | none =>
      apply selectedCutObservation_no_signature hash enc K J pp selector splice answer starts
        upperCoins forgery state hinv
      rw [hh]
      rfl
    | some sig =>
      exact selectedCutObservation_successful_splice_single hash enc K J pp selector splice
        answer starts upperCoins forgery state hinv message sig hh

/-- Every surviving output of the actual adaptive filtered interaction has the same selected-cut
observation in the global and ordinary games. The raw failed-attempt ledger stays in the source. -/
theorem selectedCutObservation_runFilteredRaw_single [SampleableType H] [SampleableType R]
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
  selectedCutObservation_splice_single hash enc K J pp selector splice answer starts upperCoins
    out.1 state (runFilteredRaw_surviving_invariant (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) adv pp splice.1 splice.2.1 threshold splice.2.2.val answer starts
        upperCoins out hout state hstate)

end GXMSS.Hypertree.SingleLayer
