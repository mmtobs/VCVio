/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Reductions.ChainUndetectability
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainMass
import all HashSig.GXMSS.Security.Reductions.ChainPreimage

/-!
# Global original-domain chain preimages

The selected cut observation compares a forged prefix with the current response at the
fixed selected cut. It uses actual retry words and current forest references, including
private successful bottom attempts whose full signatures failed. The named reduction
chooses one target before seed reveal on the common hash's original digest embedding.
-/

public section

namespace GXMSS.Hypertree.Security

open Encoding ENNReal OracleComp OracleSpec TweakableHash ChainContinuation ChainMass
open GXMSS.Security GXMSS.Hypertree.Unforgeability

variable {PP T X H M R Coins : Type} {S : Shape}

/-- The one-target PRE problem uses the common hash and its original digest-input embedding. -/
@[expose] def chainPREProblem (hash : HashInstance PP T X H S) :
    SM_DT_PRE_Problem Empty PP T X H H :=
  SM_DT_PRE_Problem.standalone hash.thf hash.digestInput hash.digestInput.injective 1

/-- Decode the selected current component under explicit endpoints and canonical references. -/
@[expose] def decodeCurrent [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S)) :
    Option (ComponentCandidate M R H S × Codeword S.v (2 ^ S.w)) := do
  let candidate ← selectedCandidate? hash family pp ends references forgery.1
    forgery.2.1 forgery.2.2
  let word ← family.value candidate.position pp candidate.message candidate.signature.randomizer
  pure (candidate, word)

/-- Actual reference words retain private bottom success after full failure. -/
@[expose] def referenceResult (metadata : Metadata R H S) (state : NativeState M H R S)
    (p : OTSPosition S) : Option (Codeword S.v (2 ^ S.w) × R) :=
  if hp : p.1.1.val = 0 then
    ((bottomLedger (H := H) state.2).find? fun entry => decide (entry.position = p)).bind
      FamilyEncoding.Record.result
  else (metadata.internalResults ⟨p, hp⟩).output

/-- Select the first smaller forged coordinate for a successful reference, or the first
nonmaximum forged coordinate and final step for an unused or exhausted reference. -/
@[expose] def chooseCurrentChain (candidate : ComponentCandidate M R H S)
    (word : Codeword S.v (2 ^ S.w)) (reference : Option (Codeword S.v (2 ^ S.w) × R)) :
    Option (ChainPosition S) :=
  match reference with
  | some wr =>
      match hi : findSmallerCoordinate wr.1 word with
      | none => none
      | some i => some (candidate.position, i, ⟨(wr.1 i).val - 1, by
          have hsmall := findSmallerCoordinate_sound wr.1 word hi
          have hbound := (wr.1 i).isLt
          omega⟩)
  | none =>
      match hi : GXMSS.Reductions.findNonMaximumCoordinate word with
      | none => none
      | some i => some (candidate.position, i, ⟨2 ^ S.w - 1 - 1, by
          have hsmall := GXMSS.Reductions.findNonMaximumCoordinate_sound word hi
          omega⟩)

/-- Component equality decides full forest-signature equality over its finite upper array. -/
@[expose] def signatureDecidableEq [DecidableEq (GXMSS.Signature R H S.h S.v)] :
    DecidableEq (Signature R H S) := fun first second =>
  decidable_of_iff (first.bottom = second.bottom ∧ first.upper = second.upper) (by
    cases first
    cases second
    simp only [Signature.mk.injEq])

/-- The current public root, strong pair freshness and complete selected opening are visible
without inspecting hidden chain starts. -/
@[expose] def cutValidityGuard [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) (metadata : Metadata R H S)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S))
    (state : NativeState M H R S) (candidate : ComponentCandidate M R H S)
    (word : Codeword S.v (2 ^ S.w)) : Bool := by
  let : DecidableEq (Signature R H S) := signatureDecidableEq
  exact verify hash family ⟨metadata.roots (topTree S), pp⟩ forgery.1 forgery.2.1 forgery.2.2 &&
    SyncSignatureUnforgeability.strongFresh state.1 forgery &&
    decide ((ends candidate.position, metadata.paths candidate.position) =
      (completedLeaf hash pp candidate word, candidate.signature.path))

/-- A selected-cut event using current validity, opening data and the fixed response. -/
@[expose] def selectedCutObservation [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (pp : PP) (selector : ChainPosition S) : Observation M H R S :=
  fun selectedResponse ends metadata references forgery state =>
    match decodeCurrent hash family pp ends references forgery with
    | none => false
    | some (candidate, word) =>
        cutValidityGuard hash family pp ends metadata forgery state candidate word &&
        if chooseCurrentChain candidate word (referenceResult metadata state candidate.position) =
            some selector then
          decide ((word selector.2.1).val < selector.2.2.val + 1 ∧
            (chainFamily hash pp).chain selector.1 selector.2.1 (word selector.2.1).val
              (selector.2.2.val + 1 - (word selector.2.1).val)
              (candidate.signature.ots selector.2.1) = selectedResponse)
        else false

/-- The forged value immediately preceding the globally selected positive chain step. -/
@[expose] def chainPredecessor (hash : HashInstance PP T X H S) (pp : PP)
    (selector : ChainPosition S) (digit : Fin (2 ^ S.w)) (ots : H) : H :=
  (chainFamily hash pp).chain selector.1 selector.2.1 digit.val
    (selector.2.2.val - digit.val) ots

/-- Prepared reference words agree with the complete actual source ledger. -/
theorem referenceResult_source [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv)) (p : OTSPosition S) :
    referenceResult (prepare hash family sampling.internal out.sk.seed out.sk.endpoints
      out.sk.upperCoins) (out.history, out.bottomAttempts) p =
      (referenceAt hash out p).bind FamilyEncoding.Record.result := by
  unfold referenceResult referenceAt
  split_ifs
  · rfl
  · rw [sourceProgram_upperResults hash family sampling adv out hout]
    rfl

/-- First-request uniqueness makes every bottom lookup retain that attempt's exact retry result. -/
theorem referenceResult_bottom_of_mem (metadata : Metadata R H S) (state : NativeState M H R S)
    (hnodup : (state.2.map BottomAttempt.epoch).Nodup)
    (attempt : BottomAttempt M R S) (hmem : attempt ∈ state.2) :
    referenceResult metadata state (bottomPosition S attempt.epoch) = attempt.result.output := by
  let p := bottomPosition S attempt.epoch
  have hsome : ((bottomLedger (H := H) state.2).find?
      fun entry => decide (entry.position = p)).isSome = true := by
    cases hf : (bottomLedger (H := H) state.2).find?
        (fun entry => decide (entry.position = p)) with
    | some entry => rfl
    | none =>
        have hall := List.find?_eq_none.mp hf
        have hm : (⟨p, bottomMessage attempt.epoch attempt.message, attempt.result.output⟩ :
            FamilyEncoding.Record M H R S) ∈ bottomLedger state.2 :=
          List.mem_map.mpr ⟨attempt, hmem, rfl⟩
        exact False.elim (hall _ hm (by simp))
  obtain ⟨entry, hf⟩ := Option.isSome_iff_exists.mp hsome
  have ht : decide (entry.position = p) = true :=
    List.find?_some (p := fun entry : FamilyEncoding.Record M H R S =>
      decide (entry.position = p)) hf
  have hposition : entry.position = p := of_decide_eq_true ht
  obtain ⟨other, hother, hentry⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
  have hep : other.epoch = attempt.epoch := positionAt_bottom_injective S
    ((congrArg FamilyEncoding.Record.position hentry).trans hposition)
  have heq := List.inj_on_of_nodup_map hnodup hother hmem hep
  subst other
  unfold referenceResult
  rw [dite_eq_left (by rfl), hf]
  simpa only [Option.bind_some] using congrArg FamilyEncoding.Record.result hentry.symm

/-- Safe raw reference digits exclude every disclosed and private selected prefix read. -/
theorem badState_eq_false_of_reference (metadata : Metadata R H S)
    (state : NativeState M H R S) (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ)
    (hnodup : (state.2.map BottomAttempt.epoch).Nodup)
    (hsafe : ∀ wr, referenceResult metadata state selected = some wr →
      threshold ≤ (wr.1 i).val) :
    badState metadata selected i threshold state = false := by
  have hprivate : privateBad metadata selected i threshold = false := by
    unfold privateBad
    split_ifs with hp
    · rfl
    · cases hr : (metadata.internalResults ⟨selected, hp⟩).output with
      | none => rfl
      | some wr =>
          have hge := hsafe wr (by simp [referenceResult, hp, hr])
          simp [hge.not_gt]
  simp only [badState, hprivate, Bool.false_or, List.any_eq_false]
  intro attempt hmem
  unfold disclosedBad
  cases hw : wordsFromResult metadata attempt.epoch attempt.result with
  | none => simp
  | some words =>
      dsimp only [Option.elim]
      have hresults := wordsFromResult_success metadata attempt.epoch attempt.result words hw
      rw [decide_eq_true_eq]
      rintro (⟨hpos, hlow⟩ | ⟨k, hpos, hlow⟩)
      · have href := referenceResult_bottom_of_mem metadata state hnodup attempt hmem
        rw [hpos, hresults.1] at href
        exact (hsafe words.1 href).not_gt hlow
      · have hp : selected.1.1.val ≠ 0 := by
          rw [← hpos]
          exact (upperPositionAt S attempt.epoch k).property
        have href : referenceResult metadata state selected = some (words.2 k) := by
          simp only [referenceResult, hp, ↓reduceDIte]
          have hupper : (⟨selected, hp⟩ : UpperPosition S) =
              upperPositionAt S attempt.epoch k := Subtype.ext hpos.symm
          rw [hupper]
          exact hresults.2 k
        exact (hsafe (words.2 k) href).not_gt hlow

/-- A designated cut is at its candidate's coordinate and never passes a successful reference. -/
theorem chooseCurrentChain_safe (candidate : ComponentCandidate M R H S)
    (word : Codeword S.v (2 ^ S.w)) (reference : Option (Codeword S.v (2 ^ S.w) × R))
    (selector : ChainPosition S) (h : chooseCurrentChain candidate word reference = some selector) :
    candidate.position = selector.1 ∧ ∀ wr, reference = some wr →
      selector.2.2.val + 1 ≤ (wr.1 selector.2.1).val := by
  unfold chooseCurrentChain at h
  cases reference with
  | none =>
      dsimp only at h
      split at h
      · contradiction
      · have heq := Option.some.inj h
        refine ⟨congrArg Prod.fst heq, ?_⟩
        intro wr hw
        contradiction
  | some wr =>
      dsimp only at h
      split at h
      · contradiction
      · rename_i i hi
        have heq := Option.some.inj h
        subst selector
        refine ⟨rfl, ?_⟩
        intro actual hactual
        have heq : actual = wr := Option.some.inj hactual.symm
        subst actual
        have hsmall := findSmallerCoordinate_sound wr.1 word hi
        dsimp only
        omega

/-- The first nonmaximum finder names exactly the final positive chain step. -/
theorem chooseCurrentChain_none (candidate : ComponentCandidate M R H S)
    (word : Codeword S.v (2 ^ S.w)) (i : Fin S.v)
    (hi : GXMSS.Reductions.findNonMaximumCoordinate word = some i) :
    chooseCurrentChain candidate word none = some (candidate.position, i,
      ⟨2 ^ S.w - 1 - 1, by
        have := GXMSS.Reductions.findNonMaximumCoordinate_sound word hi
        omega⟩) := by
  unfold chooseCurrentChain
  dsimp only
  split
  · rename_i hn
    simp_all
  · rename_i j hj
    have heq := Option.some.inj (hj.symm.trans hi)
    subst j
    rfl

/-- A successful first-smaller finder names exactly its reference digit's preceding step. -/
theorem chooseCurrentChain_some (candidate : ComponentCandidate M R H S)
    (word : Codeword S.v (2 ^ S.w)) (wr : Codeword S.v (2 ^ S.w) × R) (i : Fin S.v)
    (hi : findSmallerCoordinate wr.1 word = some i) :
    chooseCurrentChain candidate word (some wr) = some (candidate.position, i,
      ⟨(wr.1 i).val - 1, by
        have := findSmallerCoordinate_sound wr.1 word hi
        have := (wr.1 i).isLt
        omega⟩) := by
  unfold chooseCurrentChain
  dsimp only
  split
  · rename_i hn
    simp_all
  · rename_i j hj
    have heq := Option.some.inj (hj.symm.trans hi)
    subst j
    rfl

/-- Honest prepared upper references match the actual source's private fixed certificate table. -/
theorem canonicalReferences_source [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv)) :
    canonicalReferences (prepare hash family sampling.internal out.sk.seed out.sk.endpoints
      out.sk.upperCoins) (honestPrefixes hash out.sk.seed out.sk.starts) =
      sourceReferences hash out := by
  rw [canonicalReferences_honest]
  funext p
  unfold sourceReferences referenceSignatureAt referenceAt
  rw [dite_eq_right p.property]
  rw [sourceProgram_upperResults hash family sampling adv out hout]
  rfl

/-- Decoding in the honest continuation is exactly decoding the actual source forgery. -/
theorem decodeCurrent_source [SampleableType H] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv)) :
    decodeCurrent hash family out.sk.seed out.sk.endpoints
      (canonicalReferences (prepare hash family sampling.internal out.sk.seed out.sk.endpoints
        out.sk.upperCoins) (honestPrefixes hash out.sk.seed out.sk.starts)) out.forgery =
      sourceDecoded? hash family out := by
  rw [canonicalReferences_source hash family sampling adv out hout]
  rfl

/-- A source residual deterministically designates one coordinate in the full global selector. -/
@[expose] def chooseSourceChain [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Result PP H M R Coins S) : Option (ChainPosition S) := do
  let (candidate, word) ← sourceDecoded? hash family out
  chooseCurrentChain candidate word ((referenceAt hash out candidate.position).bind
    FamilyEncoding.Record.result)

/-- Fibrewise nondegeneracy supplies the unused or exhausted branch of deterministic selection. -/
theorem chooseSourceChain_complete [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (hnonmax : family.NoMaximumOutput)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv))
    (hres : sourceResidual hash family sampling out = true) :
    (chooseSourceChain hash family out).isSome = true := by
  have hc := sourceProgram_consistent hash family sampling adv out hout
  obtain ⟨candidate, word, hd, hword, hopening⟩ :=
    sourceResidual_opening hash family sampling out hc hres
  have hfinal := completedLeaf_final_cut hash family hnonmax out.sk.seed out.sk.endpoints
    candidate word hword (congrArg Prod.fst hopening)
  unfold chooseSourceChain
  rw [hd]
  change (chooseCurrentChain candidate word
    ((referenceAt hash out candidate.position).bind FamilyEncoding.Record.result)).isSome = true
  cases href : referenceAt hash out candidate.position with
  | none =>
      obtain ⟨i, hi, _, _⟩ := hfinal
      simp only [Option.bind_none, chooseCurrentChain]
      split <;> simp_all
  | some reference =>
      cases hr : reference.result with
      | none =>
          obtain ⟨i, hi, _, _⟩ := hfinal
          simp only [Option.bind_some, hr, chooseCurrentChain]
          split <;> simp_all
      | some wr =>
          obtain ⟨i, _, hi, _, _, _⟩ := sourceResidual_reference_cut hash family sampling adv out
            hout hres candidate word hd hopening reference href wr hr
          simp only [Option.bind_some, hr, chooseCurrentChain]
          split <;> simp_all

/-- The actually designated source coordinate has no private or disclosed low prefix reads. -/
theorem source_chosen_badState_eq_false [SampleableType H] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv)) (selector : ChainPosition S)
    (hchoose : chooseSourceChain hash family out = some selector) :
    badState (prepare hash family sampling.internal out.sk.seed out.sk.endpoints out.sk.upperCoins)
      selector.1 selector.2.1 (selector.2.2.val + 1) (out.history, out.bottomAttempts) = false := by
  unfold chooseSourceChain at hchoose
  cases hd : sourceDecoded? hash family out with
  | none => simp [hd] at hchoose
  | some pair =>
      rcases pair with ⟨candidate, word⟩
      rw [hd] at hchoose
      change chooseCurrentChain candidate word
        ((referenceAt hash out candidate.position).bind FamilyEncoding.Record.result) =
          some selector at hchoose
      have hs := chooseCurrentChain_safe candidate word _ selector hchoose
      apply badState_eq_false_of_reference
      · exact sourceProgram_bottomAttempts_nodup hash family sampling adv out hout
      · intro wr hwr
        rw [referenceResult_source hash family sampling adv out hout] at hwr
        exact hs.2 wr (by simpa only [hs.1] using hwr)

/-- Actual residual wins satisfy the endpoint-visible validity and opening guard. -/
theorem source_cutValidityGuard [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv))
    (hres : sourceResidual hash family sampling out = true)
    (candidate : ComponentCandidate M R H S) (word : Codeword S.v (2 ^ S.w))
    (hopening : (out.sk.endpoints candidate.position,
        (hash.componentHash candidate.position.1).authPath out.sk.seed
          (fun ep => out.sk.endpoints (candidate.position.1, ep)) candidate.position.2) =
      (completedLeaf hash out.sk.seed candidate word, candidate.signature.path)) :
    cutValidityGuard hash family out.sk.seed out.sk.endpoints
      (prepare hash family sampling.internal out.sk.seed out.sk.endpoints out.sk.upperCoins)
      out.forgery (out.history, out.bottomAttempts) candidate word = true := by
  have hc := sourceProgram_consistent hash family sampling adv out hout
  have hstrong := (sourceResidual_spec hash family sampling out hres).1
  simp only [sourceStrongObservation, SyncSignatureUnforgeability.strongValid,
    sourceObservation, scheme] at hstrong
  obtain ⟨hverify, hfresh⟩ := Bool.and_eq_true_iff.mp hstrong
  unfold cutValidityGuard
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, hopening⟩
  · simp only [verify, decide_eq_true_eq] at hverify ⊢
    simpa only [prepare, hc.1, hc.2.2] using hverify
  · simpa only [SyncSignatureUnforgeability.strongFresh, decide_eq_true_eq] using hfresh

/-- Every source residual reaches the canonical positive step selected after the forgery. -/
theorem source_residual_selectedCut [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (hnonmax : family.NoMaximumOutput)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv))
    (hres : sourceResidual hash family sampling out = true) (selector : ChainPosition S)
    (hchoose : chooseSourceChain hash family out = some selector) :
    selectedCutObservation hash family out.sk.seed selector
      (honestPrefixes hash out.sk.seed out.sk.starts selector.1 selector.2.1
        (selector.2.2.val + 1)) out.sk.endpoints
      (prepare hash family sampling.internal out.sk.seed out.sk.endpoints out.sk.upperCoins)
      (canonicalReferences (prepare hash family sampling.internal out.sk.seed out.sk.endpoints
        out.sk.upperCoins) (honestPrefixes hash out.sk.seed out.sk.starts))
      out.forgery (out.history, out.bottomAttempts) = true := by
  have hc := sourceProgram_consistent hash family sampling adv out hout
  obtain ⟨candidate, word, hd, hword, hopening⟩ :=
    sourceResidual_opening hash family sampling out hc hres
  have hchoice : chooseCurrentChain candidate word
      ((referenceAt hash out candidate.position).bind FamilyEncoding.Record.result) =
        some selector := by
    unfold chooseSourceChain at hchoose
    rw [hd] at hchoose
    exact hchoose
  unfold selectedCutObservation
  rw [decodeCurrent_source hash family sampling adv out hout, hd]
  dsimp only
  rw [source_cutValidityGuard hash family sampling adv out hout hres candidate word hopening]
  simp only [Bool.true_and]
  rw [referenceResult_source hash family sampling adv out hout, hchoice]
  simp only [↓reduceIte, decide_eq_true_eq]
  cases href : referenceAt hash out candidate.position with
  | none =>
      obtain ⟨i, hi, hsmall, hreach⟩ := completedLeaf_final_cut hash family hnonmax out.sk.seed
        out.sk.endpoints candidate word hword (congrArg Prod.fst hopening)
      simp only [href, Option.bind_none] at hchoice
      rw [chooseCurrentChain_none candidate word i hi] at hchoice
      have heq := Option.some.inj hchoice
      subst selector
      have hpositive : 0 < 2 ^ S.w - 1 := by omega
      have hcut : 2 ^ S.w - 1 - 1 + 1 = 2 ^ S.w - 1 := by omega
      dsimp only
      rw [hcut]
      refine ⟨hsmall, ?_⟩
      exact hreach.trans (by
        simpa only [honestPrefixes, endpoints, chainFamily] using
          congrFun (congrFun hc.2.1 candidate.position) i)
  | some reference =>
      cases hr : reference.result with
      | none =>
          obtain ⟨i, hi, hsmall, hreach⟩ := completedLeaf_final_cut hash family hnonmax out.sk.seed
            out.sk.endpoints candidate word hword (congrArg Prod.fst hopening)
          simp only [href, Option.bind_some, hr] at hchoice
          rw [chooseCurrentChain_none candidate word i hi] at hchoice
          have heq := Option.some.inj hchoice
          subst selector
          have hcut : 2 ^ S.w - 1 - 1 + 1 = 2 ^ S.w - 1 := by omega
          dsimp only
          rw [hcut]
          refine ⟨hsmall, ?_⟩
          exact hreach.trans (by
            simpa only [honestPrefixes, endpoints, chainFamily] using
              congrFun (congrFun hc.2.1 candidate.position) i)
      | some wr =>
          obtain ⟨i, _, hi, hsmall, _, hreach⟩ := sourceResidual_reference_cut hash family sampling
            adv out hout hres candidate word hd hopening reference href wr hr
          simp only [href, Option.bind_some, hr] at hchoice
          rw [chooseCurrentChain_some candidate word wr i hi] at hchoice
          have heq := Option.some.inj hchoice
          subst selector
          have hcut : (wr.1 i).val - 1 + 1 = (wr.1 i).val := by omega
          dsimp only
          rw [hcut]
          exact ⟨hsmall, hreach⟩

/-- Observe current honest source data after excluding every selected low prefix read. -/
@[expose] def sourceGuardedObservation (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (selector : ChainPosition S) (observe : PP → ChainPosition S → Observation M H R S)
    (out : Result PP H M R sampling.internal.Coins S) : Bool :=
  let metadata := prepare hash family sampling.internal out.sk.seed out.sk.endpoints
    out.sk.upperCoins
  let prefixes := honestPrefixes hash out.sk.seed out.sk.starts
  if badState metadata selector.1 selector.2.1 (selector.2.2.val + 1)
      (out.history, out.bottomAttempts) then false else
    observe out.sk.seed selector (prefixes selector.1 selector.2.1 (selector.2.2.val + 1))
      out.sk.endpoints metadata (canonicalReferences metadata prefixes) out.forgery
      (out.history, out.bottomAttempts)

/-- The guard observes the actual native source result after one independent global selector. -/
@[expose] noncomputable def guardedSourceProgram [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) : ProbComp Bool := do
  let selector ← sampleSelector S hv hw
  let out ← sourceProgram hash family sampling adv
  pure (sourceGuardedObservation hash family sampling selector observe out)

/-- The native guarded source event couples to the actual independent first-image experiment. -/
theorem guardedSource_mass_le_cutSource [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) :
    𝒟[guardedSourceProgram hash family sampling hv hw adv observe] {true} ≤
      𝒟[cutSourceProgram hash family sampling hv hw adv observe] {true} := by
  unfold guardedSourceProgram sourceProgram keygen
  simp only [bind_assoc, pure_bind]
  rw [OracleComp.evalDist_bind_bind_swap]
  unfold cutSourceProgram filteredCutProgram
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  rw [OracleComp.evalDist_bind_bind_swap (sampleStarts S)
    (sampleUpperCoins S sampling.sampleInternal)]
  conv_rhs =>
    rw [OracleComp.evalDist_bind_bind_swap (sampleStarts S)
      (sampleUpperCoins S sampling.sampleInternal)]
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro upperCoins _
  have hn : 0 < 2 ^ S.w - 1 := by have := selector.2.2.isLt; omega
  dsimp only
  conv_rhs =>
    rw [OracleComp.evalDist_bind_bind_swap (sampleStarts S) ($ᵗ H : ProbComp H)]
  rw [← observed_zero_real_source_mass hash family sampling adv pp selector.1 selector.2.1
    (selector.2.2.val + 1) upperCoins (observe pp selector) hn (by omega)]
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  have h := guarded_unfiltered_mass_le_observed hash family sampling adv pp selector.1
    selector.2.1 (selector.2.2.val + 1) 0
    ((chainFamily hash pp).chain selector.1 selector.2.1 0 1 (starts selector.1 selector.2.1))
    starts upperCoins (observe pp selector)
  dsimp only at h
  rw [spliceEndpoints_honest, splicePrefixes_honest, spliceOracles_honest] at h
  simpa only [runWithKeys, sourceGuardedObservation, keys, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind, prepare] using h

/-- Actual selected residual source wins pass the concrete private and public read guard. -/
theorem selectedSource_mass_le_guardedSource [SampleableType H] [DecidableEq H]
    [DecidableEq M] [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S) (hnonmax : family.NoMaximumOutput) :
    𝒟[selectedSource hash family sampling hv hw adv (sourceResidual hash family sampling)
      (chooseSourceChain hash family)] {true} ≤
      𝒟[guardedSourceProgram hash family sampling hv hw adv
        (selectedCutObservation hash family)] {true} := by
  unfold selectedSource guardedSourceProgram
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro out hout
  by_cases hsel : selectedObservation (sourceResidual hash family sampling)
      (chooseSourceChain hash family) selector out = true
  · obtain ⟨hres, hchoose⟩ := Bool.and_eq_true_iff.mp hsel
    have hc : chooseSourceChain hash family out = some selector := of_decide_eq_true hchoose
    have hgood := source_chosen_badState_eq_false hash family sampling adv out hout selector hc
    have hcut := source_residual_selectedCut hash family sampling adv hnonmax out hout hres
      selector hc
    simp [hsel, sourceGuardedObservation, hgood, hcut]
  · have hf := Bool.eq_false_iff.mpr hsel
    simp [hf]

/-- An earlier forged digit reaching the selected response gives an original-domain preimage. -/
theorem chainPredecessor_sound (hash : HashInstance PP T X H S) (pp : PP)
    (selector : ChainPosition S) (digit : Fin (2 ^ S.w)) (ots answer : H)
    (hsmall : digit.val < selector.2.2.val + 1)
    (hreach : (chainFamily hash pp).chain selector.1 selector.2.1 digit.val
      (selector.2.2.val + 1 - digit.val) ots = answer) :
    hash.thf.eval pp (hash.chainTweak selector)
      (hash.digestInput (chainPredecessor hash pp selector digit ots)) = answer := by
  have hstep := (hash.componentHash selector.1.1).chain_succ pp selector.1.2 selector.2.1
    digit.val (selector.2.2.val - digit.val) ots (by have := selector.2.2.isLt; omega)
  have hcount : selector.2.2.val - digit.val + 1 = selector.2.2.val + 1 - digit.val := by omega
  have hposition : (⟨digit.val + (selector.2.2.val - digit.val), by
      have := selector.2.2.isLt; omega⟩ : Fin (2 ^ S.w - 1)) = selector.2.2 := by
    apply Fin.ext
    change digit.val + (selector.2.2.val - digit.val) = selector.2.2.val
    omega
  rw [hcount] at hstep
  change (hash.componentHash selector.1.1).chain pp selector.1.2 selector.2.1 digit.val
    (selector.2.2.val + 1 - digit.val) ots = answer at hreach
  rw [hreach, hposition] at hstep
  exact hstep.symm

/-- Extract the actual forged predecessor from the current selected component. -/
@[expose] def extractCurrent [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (pp : PP) (selector : ChainPosition S) (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S)) : Option H :=
  (decodeCurrent hash family pp ends references forgery).map fun pair =>
    chainPredecessor hash pp selector (pair.2 selector.2.1) (pair.1.signature.ots selector.2.1)

/-- Every selected current cut event yields a concrete original-domain preimage. -/
theorem selectedCutObservation_sound [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (pp : PP) (selector : ChainPosition S) (selectedResponse : H)
    (ends : OTSPosition S → Fin S.v → H) (metadata : Metadata R H S)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S))
    (state : NativeState M H R S)
    (h : selectedCutObservation hash family pp selector selectedResponse ends metadata references
      forgery state = true) :
    ∃ preimage, extractCurrent hash family pp selector ends references forgery = some preimage ∧
      hash.thf.eval pp (hash.chainTweak selector)
        (hash.digestInput preimage) = selectedResponse := by
  cases hd : decodeCurrent hash family pp ends references forgery with
  | none => simp [selectedCutObservation, hd] at h
  | some pair =>
      rcases pair with ⟨candidate, word⟩
      have hreach : (word selector.2.1).val < selector.2.2.val + 1 ∧
          (chainFamily hash pp).chain selector.1 selector.2.1 (word selector.2.1).val
            (selector.2.2.val + 1 - (word selector.2.1).val)
            (candidate.signature.ots selector.2.1) = selectedResponse := by
        unfold selectedCutObservation at h
        rw [hd] at h
        dsimp only at h
        have hlocal := (Bool.and_eq_true_iff.mp h).2
        split_ifs at hlocal with hc
        exact of_decide_eq_true hlocal
      exact ⟨chainPredecessor hash pp selector (word selector.2.1)
        (candidate.signature.ots selector.2.1), by simp [extractCurrent, hd],
        chainPredecessor_sound hash pp selector _ _ selectedResponse hreach.1 hreach.2⟩

/-- One-target private PRE state sampled without knowing the common seed. -/
structure PREState (H Coins : Type) (S : Shape) where
  /-- One global selector. -/
  selector : ChainPosition S
  /-- Independent full start table. -/
  starts : OTSPosition S → Fin S.v → H
  /-- The fixed internal retry tapes. -/
  upperCoins : UpperPosition S → Coins
  /-- The authoritative optional challenge. -/
  answer : Option H

private noncomputable def prePick [SampleableType H]
    (hash : HashInstance PP T X H S) (sampling : RetrySampling R)
    (hv : 0 < S.v) (hw : 0 < S.w) :
    OracleComp (unifSpec + (SM_DT_PRE_challengeSpec T H +
      collectionSpec (chainPREProblem hash).thColl)) (PREState H sampling.internal.Coins S) := do
  let selector ← OracleComp.liftComp (sampleSelector S hv hw) _
  let starts ← OracleComp.liftComp (sampleStarts S) _
  let upperCoins ← OracleComp.liftComp (sampleUpperCoins S sampling.sampleInternal) _
  let answer ← liftM ((unifSpec + (SM_DT_PRE_challengeSpec T H +
    collectionSpec (chainPREProblem hash).thColl)).query (.inr (.inl (hash.chainTweak selector))))
  pure ⟨selector, starts, upperCoins, answer⟩

/-- Every failed PRE extraction returns the first chain start of the canonical top component. -/
@[expose] def canonicalPreimageFallback (starts : OTSPosition S → Fin S.v → H)
    (hv : 0 < S.v) : H := starts (topTree S, 0) ⟨0, hv⟩

/-- Invert at the selected terminal cut using the actual current forest component. -/
@[expose] def invertAt [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) (pp : PP)
    (selector : ChainPosition S) (answer : H) (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) : ProbComp H := do
  let ends := spliceEndpoints hash pp selector.1 selector.2.1 selector.2.2.val answer starts
  let metadata := prepare hash family sampling.internal pp ends upperCoins
  let references := canonicalReferences metadata
    (splicePrefixes hash pp selector.1 selector.2.1 selector.2.2.val answer starts)
  let fallback := canonicalPreimageFallback starts (by have := selector.2.1.isLt; omega)
  let out ← runFilteredRaw hash family sampling adv pp selector.1 selector.2.1
    (selector.2.2.val + 1) selector.2.2.val answer starts upperCoins
  pure (if privateBad metadata selector.1 selector.2.1 (selector.2.2.val + 1) then fallback else
    out.2.elim fallback fun state =>
      if selectedCutObservation hash family pp selector answer ends metadata references
          out.1 state then
        (extractCurrent hash family pp selector ends references out.1).getD fallback
      else fallback)

/-- The named PRE adversary uses exactly one target in the original digest input domain. -/
noncomputable def chainPreimageReduction [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S) : SM_DT_PRE_Adversary (chainPREProblem hash) where
  State := PREState H sampling.internal.Coins S
  choose := prePick hash sampling hv hw
  invert := fun state pp => match state.answer with
    | none => pure (0, canonicalPreimageFallback state.starts hv)
    | some answer => (fun preimage => (0, preimage)) <$>
        invertAt hash family sampling adv pp state.selector answer state.starts state.upperCoins

/-- The explicit native PRE program retains every original challenge and forest draw. -/
@[expose] noncomputable def explicitPREProgram [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let selector ← sampleSelector S hv hw
  let starts ← sampleStarts S
  let upperCoins ← sampleUpperCoins S sampling.sampleInternal
  let hidden ← ($ᵗ H : ProbComp H)
  let answer := hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput hidden)
  let preimage ← invertAt hash family sampling adv pp selector answer starts upperCoins
  pure (decide (hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput preimage) = answer))

/-- A fresh native PRE target has the existing original-domain challenge law. -/
private theorem preOracles_challenge [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H S) (pp : PP) (t : T) :
    (simulateQ (SM_DT_PRE_oracles (chainPREProblem hash) pp)
      (liftM ((unifSpec + (SM_DT_PRE_challengeSpec T H +
        collectionSpec (chainPREProblem hash).thColl)).query (.inr (.inl t))))).run
        (([], []) : SM_DT_PRE_State T H) =
      (fun hidden => (some (hash.thf.eval pp t (hash.digestInput hidden)),
        ([(t, hidden)], []))) <$> ($ᵗ H) :=
  GXMSS.Reductions.jointPREOracles_challenge (hash.componentHash (topTree S)) pp t

/-- Lifted preparation draws retain their exact native challenge state. -/
private theorem preOracles_liftComp [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H S) (pp : PP) {A : Type}
    (program : ProbComp A) (state : SM_DT_PRE_State T H) :
    (simulateQ (SM_DT_PRE_oracles (chainPREProblem hash) pp)
      (OracleComp.liftComp program _)).run state =
      (fun value => (value, state)) <$> program :=
  GXMSS.Reductions.jointPREOracles_liftComp (hash.componentHash (topTree S)) pp program state

/-- The named original-domain PRE experiment is exactly its explicit global forest program. -/
theorem chainPreimageReduction_experiment [SampleableType H] [DecidableEq T] [DecidableEq H]
    [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S) :
    SM_DT_PRE_Experiment (chainPreimageReduction hash family sampling hv hw adv) =
      explicitPREProgram hash family sampling hv hw adv := by
  unfold SM_DT_PRE_Experiment chainPreimageReduction prePick explicitPREProgram
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [preOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [preOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

/-- The terminal selected event is bounded by the named original-domain PRE experiment. -/
theorem cutTerminal_mass_le_PRE [SampleableType H] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S) :
    𝒟[cutTerminalProgram hash family sampling hv hw adv
      (selectedCutObservation hash family)] {true} ≤
      SM_DT_PRE_Advantage (chainPreimageReduction hash family sampling hv hw adv) := by
  change _ ≤ 𝒟[SM_DT_PRE_Experiment
    (chainPreimageReduction hash family sampling hv hw adv)] {true}
  rw [chainPreimageReduction_experiment]
  unfold cutTerminalProgram filteredCutProgram explicitPREProgram
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro pp _
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro selector _
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro starts _
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro upperCoins _
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro hidden _
  have hstep := (hash.componentHash selector.1.1).chain_succ pp selector.1.2 selector.2.1
    selector.2.2.val 0 hidden (by have := selector.2.2.isLt; omega)
  have hone : (chainFamily hash pp).chain selector.1 selector.2.1 selector.2.2.val 1 hidden =
      hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput hidden) := by
    simp only [Nat.add_zero, zero_add, GXMSS.HashInstance.chain_zero] at hstep
    exact hstep
  dsimp only
  rw [hone]
  unfold runObserved invertAt
  dsimp only
  rw [splicePrefixes_selected_cut]
  simp only [bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro out _
  by_cases hbad : privateBad (prepare hash family sampling.internal pp
      (spliceEndpoints hash pp selector.1 selector.2.1 selector.2.2.val
        (hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput hidden)) starts) upperCoins)
      selector.1 selector.2.1 (selector.2.2.val + 1) = true
  · simp [hbad]
  · simp only [hbad]
    cases hs : out.2 with
    | none => simp
    | some state =>
        dsimp only [Option.elim]
        by_cases hobs : selectedCutObservation hash family pp selector
            (hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput hidden))
            (spliceEndpoints hash pp selector.1 selector.2.1 selector.2.2.val
              (hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput hidden)) starts)
            (prepare hash family sampling.internal pp
              (spliceEndpoints hash pp selector.1 selector.2.1 selector.2.2.val
                (hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput hidden)) starts)
              upperCoins)
            (canonicalReferences (prepare hash family sampling.internal pp
              (spliceEndpoints hash pp selector.1 selector.2.1 selector.2.2.val
                (hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput hidden)) starts)
              upperCoins) (splicePrefixes hash pp selector.1 selector.2.1 selector.2.2.val
                (hash.thf.eval pp (hash.chainTweak selector) (hash.digestInput hidden)) starts))
            out.1 state = true
        · obtain ⟨preimage, hext, hpre⟩ := selectedCutObservation_sound hash family pp selector
            _ _ _ _ out.1 state hobs
          simp [hobs, hext, hpre]
        · have hf := Bool.eq_false_iff.mpr hobs
          simp [hf]

/-- Actual selected source-cut mass is bounded by the named original-domain PRE and UD games. -/
theorem cutSource_mass_le_PRE_add_UD [SampleableType H] [DecidableEq T] [DecidableEq H]
    [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S) :
    𝒟[cutSourceProgram hash family sampling hv hw adv
      (selectedCutObservation hash family)] {true} ≤
      SM_DT_PRE_Advantage (chainPreimageReduction hash family sampling hv hw adv) +
        ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (chainUndetectabilityReduction hash family sampling hv hw adv
            (selectedCutObservation hash family)) :=
  (cutSource_mass_le_terminal_add_UD hash family sampling hv hw adv
    (selectedCutObservation hash family)).trans
    (add_le_add (cutTerminal_mass_le_PRE hash family sampling hv hw adv) le_rfl)

/-- The actual residual source mass has one global forest selector and the common cut loss.
No additional component guess or signing-success conditioning occurs. -/
theorem sourceResidual_mass_le_chain [SampleableType H] [DecidableEq T] [DecidableEq H]
    [DecidableEq M] [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S) (hnonmax : family.NoMaximumOutput) :
    let : MeasurableSpace (Result PP H M R sampling.internal.Coins S) := ⊤
    𝒟[sourceProgram hash family sampling adv]
        {out | sourceResidual hash family sampling out = true} ≤
      (chainCount S : ℝ≥0∞) *
          SM_DT_PRE_Advantage (chainPreimageReduction hash family sampling hv hw adv) +
        (chainCount S : ℝ≥0∞) * ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (chainUndetectabilityReduction hash family sampling hv hw adv
            (selectedCutObservation hash family)) := by
  let : MeasurableSpace (Result PP H M R sampling.internal.Coins S) := ⊤
  have hselected := selectedSource_mass hash family sampling hv hw adv
    (sourceResidual hash family sampling) (chooseSourceChain hash family)
    (fun out hout hres => chooseSourceChain_complete hash family sampling adv hnonmax out hout hres)
  have hbound := (selectedSource_mass_le_guardedSource hash family sampling hv hw adv hnonmax).trans
    ((guardedSource_mass_le_cutSource hash family sampling hv hw adv
      (selectedCutObservation hash family)).trans
      (cutSource_mass_le_PRE_add_UD hash family sampling hv hw adv))
  rw [hselected] at hbound
  have hcard : chainCount S ≠ 0 := by
    rw [← card_chainPosition S]
    let : SampleableType (ChainPosition S) := selectorSampling S hv hw
    exact Nat.card_pos.ne'
  have hzero : (chainCount S : ℝ≥0∞) ≠ 0 := by exact_mod_cast hcard
  have h := mul_le_mul_right hbound (chainCount S : ℝ≥0∞)
  rw [ENNReal.mul_inv_cancel_left hzero (ENNReal.natCast_ne_top _)] at h
  simpa only [mul_add, mul_assoc] using h

end GXMSS.Hypertree.Security
