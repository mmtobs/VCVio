/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
public import HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all HashSig.GXMSS.Hypertree.SingleLayer
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainMass
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainContinuation
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses
import all HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all VCVio.CryptoFoundations.SyncSignatureAlg
import all HashSig.GXMSS.Security.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Reductions.ChainUndetectability

/-!
# Depth-one chain challenge and splice coordinates

These laws transport actual original-domain challenges, uniform global selectors and every
spliced prefix through the unique component coordinate. The adaptive IID splice law retains
optional full histories and raw keys while hiding only private retry metadata and killed outputs.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash MeasureTheory ProbabilityTheory

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Forget exactly the unique component coordinate of one global positive chain position. -/
@[expose] def chainPositionEquiv :
    ChainPosition (singleShape h w v) ≃ GXMSS.Reductions.Guess h w v :=
  Equiv.prodCongr otsEquiv (Equiv.refl _)

/-- Global selection retains the original local epoch, chain label and positive-step index. -/
@[simp] theorem chainPositionEquiv_apply (selector : ChainPosition (singleShape h w v)) :
    chainPositionEquiv selector = (selector.1.2, selector.2) := rfl

/-- The depth-one PRE problem is the identical original-domain native hardness problem. -/
theorem chainPREProblem_single (hash : GXMSS.HashInstance PP T X H h w v) :
    Security.chainPREProblem (liftHash hash) = GXMSS.Reductions.chainPREProblem hash := rfl

/-- The depth-one UD problem preserves both native worlds and their original domain. -/
theorem chainUDProblem_single [SampleableType H]
    (hash : GXMSS.HashInstance PP T X H h w v) :
    Security.chainUDProblem (liftHash hash) = GXMSS.Reductions.chainUDProblem hash := rfl

/-- Each world's actual challenge response is unchanged by the full-coordinate observation. -/
theorem chainUD_response_single [SampleableType H]
    (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (selector : ChainPosition (singleShape h w v)) (world : SM_DT_UD_World) :
    SM_DT_UD_response world (Security.chainUDProblem (liftHash hash)) pp
        ((liftHash hash).chainTweak selector) =
      SM_DT_UD_response world (GXMSS.Reductions.chainUDProblem hash) pp
        (hash.chainTweak (chainPositionEquiv selector)) := rfl

/-- The global canonical total PRE fallback becomes the old leaf-zero, chain-zero fallback. -/
theorem canonicalPreimageFallback_single
    (starts : OTSPosition (singleShape h w v) → Fin v → H) (hv : 0 < v) :
    Security.canonicalPreimageFallback starts hv = startsEquiv starts 0 ⟨0, hv⟩ := rfl

/-- Reindexing the actual global uniform selector yields the old complete-tree selector law. -/
theorem sampleSelector_evalDistEq [NeZero v] [NeZero (2 ^ w - 1)]
    (hv : 0 < v) (hw : 0 < w) :
    chainPositionEquiv <$> Security.ChainMass.sampleSelector (singleShape h w v) hv hw =ᵈ
      ($ᵗ (GXMSS.Reductions.Guess h w v)) := by
  let : MeasurableSpace (ChainPosition (singleShape h w v)) := ⊤
  let : MeasurableSpace (GXMSS.Reductions.Guess h w v) := ⊤
  let : SampleableType (ChainPosition (singleShape h w v)) :=
    Security.ChainMass.selectorSampling _ hv hw
  apply EvalDistEq.of_evalDist_eq
  rw [evalDist_map_of_discrete]
  change (𝒟[($ᵗ (ChainPosition (singleShape h w v)))]).map chainPositionEquiv = _
  rw [SampleableType.evalDist_uniformSample, SampleableType.evalDist_uniformSample]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete chainPositionEquiv.bijective

/-- Every depth-one spliced prefix is the old complete-tree splice at the observed coordinate. -/
theorem splicePrefixes_single (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (selector : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (ep : Fin (2 ^ h)) (i : Fin v) (position : ℕ) :
    Security.ChainContinuation.splicePrefixes (liftHash hash) pp selector.1 selector.2.1
        selector.2.2.val answer starts (topTree _, ep) i position =
      if ep = selector.1.2 ∧ i = selector.2.1 then
        if position < selector.2.2.val + 1 then
          hash.chain pp ep i 0 position (startsEquiv starts ep i)
        else hash.chain pp ep i (selector.2.2.val + 1)
          (position - (selector.2.2.val + 1)) answer
      else hash.chain pp ep i 0 position (startsEquiv starts ep i) := by
  have heq : ((topTree (singleShape h w v), ep) : OTSPosition (singleShape h w v)) =
      selector.1 ↔ ep = selector.1.2 := by
    constructor
    · exact congrArg Prod.snd
    · intro hep
      exact Prod.ext (Subsingleton.elim _ _) hep
  simp only [Security.ChainContinuation.splicePrefixes,
    GXMSS.Reductions.ChainContinuation.spliceValue, heq,
    Security.ChainContinuation.chainFamily, componentHash_liftHash, startsEquiv_apply]
  split_ifs <;> rfl

/-- The full bottom retry metadata uses the same IID tape and ordinary epoch. -/
theorem bottomResult_iid_single [SampleableType R]
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pp : PP) (ep : Epoch (singleShape h w v)) (msg : M)
    (coins : (RetryPlan.iid R K).Coins) :
    Security.ChainContinuation.bottomResult (familyOfEncoding (H := H) enc) (RetryPlan.iid R K)
      pp ep msg coins = (RetryPlan.iid R K).run enc pp msg (epochEquiv ep) coins := by
  apply RetryPlan.run_eq_of_values_eq
  intro i
  simp only [Encoding.Family.value_atEpoch, familyOfEncoding_value,
    messageEquiv_bottomMessage]
  exact congrArg (enc.value pp msg ((RetryPlan.iid R K).randomizers coins i))
    (otsEquiv_bottomPosition ep)

/-- Spliced endpoints preserve every complete ordinary leaf vector. -/
private theorem spliceEndpoints_single (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (selector : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H) :
    startsEquiv (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp
      selector.1 selector.2.1 selector.2.2.val answer starts) =
      GXMSS.Reductions.splicedEndpoints hash pp (chainPositionEquiv selector) answer
        (startsEquiv starts) := by
  funext ep i
  exact splicePrefixes_single hash pp selector answer starts ep i (2 ^ w - 1)

/-- Each complete component materializes the identical spliced signature. -/
private theorem spliceComponent_single
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (plan : RetryPlan R) (pp : PP)
    (selector : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → plan.Coins)
    (ep : Epoch (singleShape h w v)) (wr : Codeword v (2 ^ w) × R) :
    Security.ChainContinuation.component
      (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc) plan pp
        (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp selector.1
          selector.2.1 selector.2.2.val answer starts) upperCoins)
      (Security.ChainContinuation.splicePrefixes (liftHash hash) pp selector.1 selector.2.1
        selector.2.2.val answer starts) (bottomPosition _ ep) wr =
      GXMSS.Reductions.splicedSignatureOfWord hash pp (chainPositionEquiv selector) answer
        (startsEquiv starts)
        (GXMSS.Reductions.splicedEndpoints hash pp (chainPositionEquiv selector) answer
          (startsEquiv starts)) (epochEquiv ep) wr := by
  unfold Security.ChainContinuation.component GXMSS.Reductions.splicedSignatureOfWord
  congr 1
  · funext i
    rw [bottomPosition_eq, splicePrefixes_single]
    rfl
  · simp only [Security.ChainContinuation.prepare, componentHash_liftHash,
      bottomPosition_eq]
    rw [← spliceEndpoints_single]
    rfl

/-- Fixed IID tapes preserve the optional spliced signature, including retry exhaustion. -/
private theorem spliceSign_iid_single [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (selector : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (ep : Epoch (singleShape h w v)) (msg : M) (coins : (RetryPlan.iid R K).Coins) :
    Option.map signatureEquiv
      (Security.ChainContinuation.spliceSign (liftHash hash) (familyOfEncoding enc)
        (RetrySampling.iid K J) pp selector.1 selector.2.1 selector.2.2.val answer
          starts upperCoins ep msg coins) =
      ((RetryPlan.iid R K).run enc pp msg (epochEquiv ep) coins).output.map
        (GXMSS.Reductions.splicedSignatureOfWord hash pp (chainPositionEquiv selector) answer
          (startsEquiv starts)
          (GXMSS.Reductions.splicedEndpoints hash pp (chainPositionEquiv selector) answer
            (startsEquiv starts)) (epochEquiv ep)) := by
  dsimp only [RetrySampling.iid]
  unfold Security.ChainContinuation.spliceSign Security.ChainContinuation.materialize
  rw [bottomResult_iid_single]
  cases ((RetryPlan.iid R K).run enc pp msg (epochEquiv ep) coins).output with
  | none => rfl
  | some wr =>
    change some (Security.ChainContinuation.component
      (S := singleShape h w v) _ _ _ wr) = _
    rw [spliceComponent_single]
    rfl

/-- At depth one there is no private certificate that can kill a chain simulation. -/
@[simp] theorem privateBad_single (metadata : Security.ChainContinuation.Metadata R H
    (singleShape h w v)) (selected : OTSPosition (singleShape h w v))
    (i : Fin v) (threshold : ℕ) :
    Security.ChainMass.privateBad metadata selected i threshold = false := by
  simp [Security.ChainMass.privateBad]

/-- A complete depth-one disclosure guard reads only the bottom retry output. -/
theorem disclosedBad_single (metadata : Security.ChainContinuation.Metadata R H
    (singleShape h w v)) (selected : OTSPosition (singleShape h w v))
    (i : Fin v) (threshold : ℕ)
    (attempt : Security.BottomAttempt M R (singleShape h w v)) :
    Security.ChainMass.disclosedBad metadata selected i threshold attempt =
      attempt.result.output.elim false (fun wr =>
        decide (epochEquiv attempt.epoch = selected.2 ∧ (wr.1 i).val < threshold)) := by
  unfold Security.ChainMass.disclosedBad Security.ChainContinuation.wordsFromResult
  cases attempt.result.output with
  | none => rfl
  | some wr =>
    change decide ((bottomPosition _ attempt.epoch = selected ∧ _) ∨
      ∃ k : Fin 0, _) = _
    simp only [bottomPosition_eq]
    congr 1
    apply propext
    simp [Prod.ext_iff, tree_eq_top selected.1]

private theorem spliceSign_iid_lift_single [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (ep : Epoch (singleShape h w v)) (msg : M) (coins : (RetryPlan.iid R K).Coins) :
    Security.ChainContinuation.spliceSign (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) pp splice.1 splice.2.1 splice.2.2.val answer
        starts upperCoins ep msg coins =
      ((RetryPlan.iid R K).run enc pp msg (epochEquiv ep) coins).output.map
        (fun wr => signatureEquiv.symm
          (GXMSS.Reductions.splicedSignatureOfWord hash pp (chainPositionEquiv splice) answer
            (startsEquiv starts)
            (GXMSS.Reductions.splicedEndpoints hash pp (chainPositionEquiv splice) answer
              (startsEquiv starts)) (epochEquiv ep) wr)) := by
  have heq := congrArg (Option.map (signatureEquiv (w := w)).symm)
    (spliceSign_iid_single hash enc K J pp splice answer starts upperCoins ep msg coins)
  have hback : (signatureEquiv (R := R) (H := H) (h := h) (w := w) (v := v)).symm ∘
      signatureEquiv = id := Equiv.symm_comp_self _
  rw [Option.map_map, Option.map_map, hback, Option.map_id] at heq
  exact heq


private def ordinaryFilteredOracles [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (GXMSS.Signature R H h v))) ProbComp) :=
  QueryImpl.add ((fun (q : ℕ) (state : Option (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))) => match state with
    | none => pure ((0 : Fin (q + 1)), none)
    | some history => (fun answer => (answer, some history)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) q) :
    QueryImpl unifSpec (StateT (Option (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))) ProbComp))
    (GXMSS.Reductions.filteredSplicedSigningOracle hash enc K pp
      (chainPositionEquiv selector) (chainPositionEquiv splice) answer (startsEquiv starts)
      (GXMSS.Reductions.splicedEndpoints hash pp (chainPositionEquiv splice) answer
        (startsEquiv starts)))

private theorem filteredOracles_run
    (original : QueryImpl (Security.ChainMass.FullSpec M H R (singleShape h w v))
      (StateT (Security.NativeState M H R (singleShape h w v)) ProbComp))
    (bad : Security.NativeState M H R (singleShape h w v) → Bool)
    (q : (Security.ChainMass.FullSpec M H R (singleShape h w v)).Domain)
    (state : Option (Security.NativeState M H R (singleShape h w v))) :
    (Security.ChainMass.filteredOracles original bad q).run state =
      match state with
      | none => pure (Security.ChainMass.dummy q, none)
      | some s => (fun out =>
          (if bad out.2 then Security.ChainMass.dummy q else out.1,
            if bad out.2 then none else some out.2)) <$> (original q).run s := by
  cases state <;> simp only [Security.ChainMass.filteredOracles, StateT.run]

private theorem oldFiltered_run [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pp : PP) (selector splice : GXMSS.Reductions.Guess h w v) (answer : H)
    (starts ends : Fin (2 ^ h) → Fin v → H) (ep : Fin (2 ^ h)) (msg : M)
    (state : Option (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))) :
    (GXMSS.Reductions.filteredSplicedSigningOracle hash enc K pp selector splice answer
      starts ends (ep, msg)).run state = (match state with
      | none => pure (none, none)
      | some history => match history ep with
        | some _ => pure (none, some history)
        | none => do
          let wr ← enc.retry ($ᵗ R) pp msg ep K
          match wr with
          | none => pure (none, some (Function.update history ep (some (msg, none))))
          | some value =>
            if ep = GXMSS.Reductions.guessedEpoch selector ∧
                (value.1 (GXMSS.Reductions.guessedChain selector)).val <
                  (GXMSS.Reductions.guessedPosition selector).val + 1 then
              pure (none, none)
            else
              let sig := GXMSS.Reductions.splicedSignatureOfWord hash pp splice answer
                starts ends ep value
              pure (some sig, some (Function.update history ep (some (msg, some sig))))) := by
  unfold GXMSS.Reductions.filteredSplicedSigningOracle
  rfl

private theorem filteredSpliceOracles_iid_projection [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (q : (Security.ChainMass.FullSpec M H R (singleShape h w v)).Domain)
    (state : Option (Security.NativeState M H R (singleShape h w v)))
    (hgood : ∀ s, state = some s →
      Security.ChainMass.badState
        (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
          (RetryPlan.iid R J) pp
          (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
            splice.2.1 splice.2.2.val answer starts) upperCoins)
        splice.1 splice.2.1 (selector.2.2.val + 1) s = false)
    (hselected : splice.1 = selector.1) (hchain : splice.2.1 = selector.2.1) :
    Prod.map id (Option.map (fun s => historyObservation s.1)) <$>
      (Security.ChainMass.filteredSpliceOracles (liftHash hash) (familyOfEncoding enc)
        (RetrySampling.iid K J) pp splice.1 splice.2.1 (selector.2.2.val + 1)
          splice.2.2.val answer starts upperCoins q).run state =ᵈ
      (simulateQ (ordinaryFilteredOracles hash enc K pp selector splice answer starts)
        (queryBridge q)).run (state.map (fun s => historyObservation s.1)) := by
  dsimp only [RetrySampling.iid] at *
  unfold Security.ChainMass.filteredSpliceOracles
  rw [filteredOracles_run (w := w)]
  cases q with
  | inl uniform =>
    simp only [queryBridge, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, ordinaryFilteredOracles, QueryImpl.add]
    cases state with
    | none => simp [StateT.run, Security.ChainMass.dummy]
    | some s =>
      have hg := hgood s rfl
      simp only [Security.ChainMass.spliceOracles, Security.ChainMass.oraclesWithAttempts,
        QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
      simp [StateT.run, hg]
  | inr request =>
    rcases request with ⟨ep, msg⟩
    simp only [queryBridge, simulateQ_map, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, ordinaryFilteredOracles, QueryImpl.add, StateT.run_map]
    rw [oldFiltered_run]
    cases state with
    | none => simp [Security.ChainMass.dummy]
    | some s =>
      have hg := hgood s rfl
      simp only [Security.ChainMass.spliceOracles, Security.ChainMass.oraclesWithAttempts,
        QueryImpl.add_apply_inr, StateT.run, Security.signingOracleWithAttempts]
      cases hused : s.1 ep with
      | some entry =>
        have ho : historyObservation s.1 (epochEquiv ep) =
            some (entry.1, entry.2.map signatureEquiv) := by
          simp [historyObservation, hused]
        simp [ho, hg]
      | none =>
        have ho : historyObservation s.1 (epochEquiv ep) = none := by
          simp [historyObservation, hused]
        have hprior : s.2.any (Security.ChainMass.disclosedBad
            (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
              (RetryPlan.iid R J) pp
              (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
                splice.2.1 splice.2.2.val answer starts) upperCoins)
            splice.1 splice.2.1 (selector.2.2.val + 1)) = false := by
          simpa only [Security.ChainMass.badState, privateBad_single, Bool.false_or] using hg
        simp only [ho, Option.map_some, map_bind, map_pure,
          Security.ChainMass.badState, privateBad_single, Bool.false_or, List.any_append,
          List.any_cons, List.any_nil, Bool.or_false, hprior, Bool.false_or,
          disclosedBad_single]
        have hsign := fun coins => spliceSign_iid_lift_single hash enc K J pp splice answer
          starts upperCoins ep msg coins
        dsimp only [RetrySampling.iid] at hsign
        simp only [bottomResult_iid_single, hsign]
        refine EvalDistEq.trans ?_
          ((RetryPlan.iid_run_output_evalDistEq_retry enc pp msg (epochEquiv ep) K).bind_left _)
        simp only [bind_map_left]
        apply EvalDistEq.bind_right
        intro coins
        cases hwr : ((RetryPlan.iid R K).run enc pp msg (epochEquiv ep) coins).output with
        | none =>
          simp [Prod.map, (historyObservation_update (w := w))]
        | some wr =>
          simp only [Option.elim_some, Option.map_some]
          by_cases hkill : epochEquiv ep = splice.1.2 ∧
              (wr.1 splice.2.1).val < selector.2.2.val + 1
          · simp [hkill, Security.ChainMass.dummy, Prod.map,
              GXMSS.Reductions.guessedEpoch, GXMSS.Reductions.guessedChain,
              GXMSS.Reductions.guessedPosition, chainPositionEquiv, otsEquiv, ← hselected, ← hchain]
          · simp only [Nat.lt_add_one_iff] at hkill
            simp [hkill, Prod.map, (historyObservation_update (w := w)),
              GXMSS.Reductions.guessedEpoch, GXMSS.Reductions.guessedChain,
              GXMSS.Reductions.guessedPosition, chainPositionEquiv, otsEquiv, ← hselected, ← hchain]


private theorem filteredOracles_preserves_good
    (original : QueryImpl (Security.ChainMass.FullSpec M H R (singleShape h w v))
      (StateT (Security.NativeState M H R (singleShape h w v)) ProbComp))
    (bad : Security.NativeState M H R (singleShape h w v) → Bool) :
    QueryImpl.PreservesInv (Security.ChainMass.filteredOracles original bad)
      (fun state => ∀ s, state = some s → bad s = false) := by
  intro q state _ out hout s hs
  cases state with
  | none =>
    simp only [filteredOracles_run, support_pure, Set.mem_singleton_iff] at hout
    subst out
    cases hs
  | some state =>
    rw [filteredOracles_run] at hout
    simp only [support_map, Set.mem_image] at hout
    obtain ⟨next, _, hnext⟩ := hout
    subst out
    by_cases hbad : bad next.2 = true
    · simp [hbad] at hs
    · have hg : bad next.2 = false := Bool.eq_false_iff.mpr hbad
      simp only [hg, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
      simpa only [← hs] using hg

/-- The full adaptive filtered IID run preserves every surviving response and history.
The private bottom-attempt log is projected only after its rejection guard has been applied. -/
private theorem filtered_run_iid_projection [SampleableType R] {A : Type}
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (program : OracleComp (Security.ChainMass.FullSpec M H R (singleShape h w v)) A)
    (state : Option (Security.NativeState M H R (singleShape h w v)))
    (hgood : ∀ s, state = some s →
      Security.ChainMass.badState
        (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
          (RetryPlan.iid R J) pp
          (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
            splice.2.1 splice.2.2.val answer starts) upperCoins)
        splice.1 splice.2.1 (selector.2.2.val + 1) s = false)
    (hselected : splice.1 = selector.1) (hchain : splice.2.1 = selector.2.1) :
    Prod.map id (Option.map (fun s => historyObservation s.1)) <$>
      (simulateQ (Security.ChainMass.filteredSpliceOracles (liftHash hash)
        (familyOfEncoding enc) (RetrySampling.iid K J) pp splice.1 splice.2.1
          (selector.2.2.val + 1) splice.2.2.val answer starts upperCoins) program).run state =ᵈ
      (simulateQ (ordinaryFilteredOracles hash enc K pp selector splice answer starts)
        (simulateQ queryBridge program)).run (state.map (fun s => historyObservation s.1)) := by
  rw [← QueryImpl.simulateQ_compose]
  apply GXMSS.Reductions.FilteredSimulation.map_simulateQ_run_evalDistEq_of_query
    (inv := fun state => ∀ s, state = some s →
      Security.ChainMass.badState
        (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
          (RetryPlan.iid R J) pp
          (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
            splice.2.1 splice.2.2.val answer starts) upperCoins)
        splice.1 splice.2.1 (selector.2.2.val + 1) s = false)
  · exact filteredOracles_preserves_good _ _
  · intro q state hg
    exact filteredSpliceOracles_iid_projection hash enc K J pp selector splice answer starts
      upperCoins q state hg hselected hchain
  · exact hgood

private def ordinaryOriginalOracles [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
        (GXMSS.Signature R H h v))) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (Option (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))) ProbComp) +
    GXMSS.Reductions.filteredSplicedSigningOracle hash enc K pp
      (chainPositionEquiv selector) (chainPositionEquiv splice) answer (startsEquiv starts)
      (GXMSS.Reductions.splicedEndpoints hash pp (chainPositionEquiv splice) answer
        (startsEquiv starts))

private theorem ordinaryFiltered_masked_run [SampleableType R] {A : Type}
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) A)
    (state : Option (SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))) :
    (fun out => out.2.map (fun history => (out.1, history))) <$>
      (simulateQ (ordinaryFilteredOracles hash enc K pp selector splice answer starts)
        program).run state =ᵈ
    (fun out => out.2.map (fun history => (out.1, history))) <$>
      (simulateQ (ordinaryOriginalOracles hash enc K pp selector splice answer starts)
        program).run state := by
  apply GXMSS.Reductions.FilteredSimulation.masked_simulateQ_run_evalDistEq
  · intro q out hout
    cases q with
    | inl uniform =>
      simp only [ordinaryFilteredOracles, QueryImpl.add, StateT.run] at hout
      simp only [support_pure, Set.mem_singleton_iff] at hout
      subst out
      rfl
    | inr request =>
      rcases request with ⟨ep, msg⟩
      simp only [ordinaryFilteredOracles, QueryImpl.add, StateT.run,
        GXMSS.Reductions.filteredSplicedSigningOracle] at hout
      simp only [support_pure, Set.mem_singleton_iff] at hout
      subst out
      rfl
  · intro q out hout
    cases q with
    | inl uniform =>
      simp only [ordinaryOriginalOracles, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, StateT.run_monadLift] at hout
      simp only [mem_support_bind_iff] at hout
      obtain ⟨answer, _, heq⟩ := hout
      simp only [support_pure, Set.mem_singleton_iff] at heq
      subst out
      rfl
    | inr request =>
      rcases request with ⟨ep, msg⟩
      simp only [ordinaryOriginalOracles, QueryImpl.add_apply_inr, StateT.run,
        GXMSS.Reductions.filteredSplicedSigningOracle] at hout
      simp only [support_pure, Set.mem_singleton_iff] at hout
      subst out
      rfl
  · intro q history
    cases q with
    | inl uniform =>
      simp only [ordinaryFilteredOracles, ordinaryOriginalOracles, QueryImpl.add]
      simp only [StateT.run, map_eq_bind_pure_comp]
      rfl
    | inr request => rfl

/-- The optional ordinary raw-key result of a surviving depth-one splice interaction. -/
@[expose] def spliceResultObservation (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (starts ends : OTSPosition (singleShape h w v) → Fin v → H)
    (out : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)) ×
        Option (Security.NativeState M H R (singleShape h w v))) :
    Option (GXMSS.Reductions.Result PP H M R h v) :=
  out.2.map fun state =>
    ⟨⟨hash.merkleRoot pp (startsEquiv ends), pp⟩,
      ⟨pp, startsEquiv starts, startsEquiv ends⟩,
      forgeryObservation out.1, historyObservation state.1⟩

/-- Complete filtered adaptive signing agrees with the ordinary splice after hiding only
private metadata and every adversarial output in the absorbing killed state. -/
private theorem runFilteredRaw_iid_single [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (hselected : splice.1 = selector.1) (hchain : splice.2.1 = selector.2.1) :
    spliceResultObservation hash pp starts
      (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1 splice.2.1
        splice.2.2.val answer starts) <$>
      Security.ChainMass.runFilteredRaw (liftHash hash) (familyOfEncoding enc)
        (RetrySampling.iid K J) adv pp splice.1 splice.2.1 (selector.2.2.val + 1)
          splice.2.2.val answer starts upperCoins =ᵈ
      GXMSS.Reductions.runFilteredSpliced hash enc K (adversaryToOrdinary adv) pp
        (chainPositionEquiv selector) (chainPositionEquiv splice) answer (startsEquiv starts) := by
  let ends := Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
    splice.2.1 splice.2.2.val answer starts
  let metadata := Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
    (RetryPlan.iid R J) pp ends upperCoins
  let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp (startsEquiv ends), pp⟩
  let initial : Option (Security.NativeState M H R (singleShape h w v)) :=
    some (SyncSignatureUnforgeability.emptyHistory, [])
  have hgood : ∀ s, initial = some s →
      Security.ChainMass.badState metadata splice.1 splice.2.1 (selector.2.2.val + 1) s =
        false := by
    intro state hstate
    simp only [initial, Option.some.injEq] at hstate
    subst state
    simp [Security.ChainMass.badState]
  have hrun := (filtered_run_iid_projection hash enc K J pp selector splice answer starts
    upperCoins (adv.forge pk) initial hgood hselected hchain).map
      (fun out => out.2.map fun history =>
        (⟨pk, ⟨pp, startsEquiv starts, startsEquiv ends⟩, forgeryObservation out.1, history⟩ :
          GXMSS.Reductions.Result PP H M R h v))
  have hmask := (ordinaryFiltered_masked_run hash enc K pp selector splice answer starts
    (simulateQ queryBridge (adv.forge pk))
    (some SyncSignatureUnforgeability.emptyHistory)).map
      (Option.map fun pair =>
        (⟨pk, ⟨pp, startsEquiv starts, startsEquiv ends⟩,
          forgeryObservation pair.1, pair.2⟩ : GXMSS.Reductions.Result PP H M R h v))
  have hroot : metadata.roots (topTree _) = pk.root := by
    simp only [metadata, Security.ChainContinuation.prepare, componentRoot_eq, pk]
    rfl
  have hempty : historyObservation
      (SyncSignatureUnforgeability.emptyHistory : SyncSignatureUnforgeability.History
        (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) =
      SyncSignatureUnforgeability.emptyHistory := rfl
  simp only [Functor.map_map, Option.map_map, Option.map_some, Prod.map, Function.id_def,
    initial, hempty] at hrun hmask
  unfold Security.ChainMass.runFilteredRaw
  dsimp only [RetrySampling.iid]
  change spliceResultObservation hash pp starts ends <$>
    (simulateQ (Security.ChainMass.filteredSpliceOracles (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) pp splice.1 splice.2.1
      (selector.2.2.val + 1) splice.2.2.val answer starts upperCoins)
      (adv.forge ⟨metadata.roots (topTree _), pp⟩)).run
      (if Security.ChainMass.badState metadata splice.1 splice.2.1
        (selector.2.2.val + 1) (SyncSignatureUnforgeability.emptyHistory, []) then none
        else initial) =ᵈ _
  rw [hgood _ rfl, hroot]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply hrun.trans
  apply hmask.trans
  unfold GXMSS.Reductions.runFilteredSpliced
  simp only [adversaryToOrdinary]
  simp only [simulateQ_map, StateT.run_map]
  unfold ordinaryOriginalOracles
  simp only [← spliceEndpoints_single]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply EvalDistEq.bind_right
  rintro ⟨forgery, history⟩
  cases history <;> rfl


/-- The endpoint-visible guard is exactly the old complete-opening strong-source guard at
depth one, including its behavior on arbitrary invalid or replayed signatures. -/
theorem cutValidityGuard_single [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (out : Security.Result PP H M R (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v))
    (hseed : out.pk.seed = out.sk.seed)
    (hroot : out.pk.root = componentRoot (liftHash hash) out.sk.seed out.sk.endpoints (topTree _))
    (word : Codeword v (2 ^ w))
    (hword : enc.value out.sk.seed out.forgery.2.1 out.forgery.2.2.bottom.randomizer
      (epochEquiv out.forgery.1) = some word) :
    Security.cutValidityGuard (liftHash hash) (familyOfEncoding enc) out.sk.seed out.sk.endpoints
        (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
          (RetrySampling.iid K J).internal out.sk.seed out.sk.endpoints out.sk.upperCoins)
        out.forgery (out.history, out.bottomAttempts)
        ⟨bottomPosition _ out.forgery.1, bottomMessage out.forgery.1 out.forgery.2.1,
          out.forgery.2.2.bottom⟩ word =
      GXMSS.Reductions.gameOneObservation hash enc K (enrichedSourceObservation out) := by
  let : DecidableEq (Signature R H (singleShape h w v)) := Security.signatureDecidableEq
  have hpk : out.pk =
      ⟨componentRoot (liftHash hash) out.sk.seed out.sk.endpoints (topTree _), out.sk.seed⟩ := by
    calc
      out.pk = ⟨out.pk.root, out.pk.seed⟩ := rfl
      _ = _ := by rw [hseed, hroot]
  have hstrong := strongValid_observation hash enc K J (out.pk, out.forgery, out.history)
  unfold Security.cutValidityGuard
  change ((verify (liftHash hash) (familyOfEncoding enc)
      ⟨componentRoot (liftHash hash) out.sk.seed out.sk.endpoints (topTree _), out.sk.seed⟩
      out.forgery.1 out.forgery.2.1 out.forgery.2.2 &&
      SyncSignatureUnforgeability.strongFresh out.history out.forgery) && (_ : Bool)) = _
  rw [← hpk]
  change (SyncSignatureUnforgeability.strongValid
      (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J))
      (out.pk, out.forgery, out.history) && (_ : Bool)) = _
  rw [← hstrong]
  simp only [GXMSS.Reductions.gameOneObservation, GXMSS.Reductions.forgedLeaf?,
    enrichedSourceObservation, forgeryObservation, interactionObservation,
    secretKeyEquiv_endpoints, signatureEquiv_apply, hseed, hword,
    Option.map_some, Security.ChainContinuation.prepare,
    componentHash_liftHash, bottomPosition_eq, startsEquiv_apply]
  unfold GXMSS.Hypertree.Unforgeability.completedLeaf
  simp only [componentHash_liftHash, bottomPosition_eq]
  rfl

end GXMSS.Hypertree.SingleLayer
