/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerCutObservation
public import HashSig.GXMSS.Security.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
import all HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Reductions.ChainUndetectability
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Auxiliary.ChainSourceMass

/-!
# Complete depth-one PRE and UD experiment transports

The original-domain games retain both Boolean outcomes, including successful canonical
fallbacks after killed or invalid signing interactions.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash MeasureTheory

variable {PP T X H M R : Type} {h w v : ℕ}

private theorem bool_evalDistEq_of_true (left right : ProbComp Bool)
    (htrue : 𝒟[left] {true} = 𝒟[right] {true}) : left =ᵈ right := by
  apply EvalDistEq.of_evalDist_eq
  apply Measure.ext_of_singleton
  intro result
  cases result with
  | true => exact htrue
  | false =>
    have hcompl : ({true} : Set Bool)ᶜ = {false} := by
      ext b
      cases b <;> simp
    rw [← hcompl, measure_compl (measurableSet_singleton true) (measure_ne_top _ _),
      measure_compl (measurableSet_singleton true) (measure_ne_top _ _)]
    simp [htrue]

private theorem singleLayerStartDraws_evalDistEq [SampleableType H] {A Coins : Type}
    (sample : ProbComp Coins)
    (finish : (Fin (2 ^ h) → Fin v → H) → ProbComp A) :
    (do
      let starts ← sampleStarts (singleShape h w v)
      let _ ← sampleUpperCoins (singleShape h w v) sample
      finish (startsEquiv starts)) =ᵈ
    (GXMSS.sampleStarts H h v >>= finish) := by
  calc
    _ =ᵈ ((do
        let starts ← sampleStarts (singleShape h w v)
        finish (startsEquiv starts)) : ProbComp A) := by
      apply EvalDistEq.bind_right
      intro starts
      exact EvalDistEq.bind_const _ _
    _ =ᵈ _ := by
      simpa only [bind_map_left] using
        (sampleStarts_evalDistEq (H := H) (h := h) (w := w) (v := v)).bind_left finish

private theorem singleLayerDraws_evalDistEq [SampleableType H]
    [NeZero v] [NeZero (2 ^ w - 1)] {A Coins : Type}
    (hv : 0 < v) (hw : 0 < w) (sample : ProbComp Coins)
    (finish : GXMSS.Reductions.Guess h w v → (Fin (2 ^ h) → Fin v → H) → ProbComp A) :
    (do
      let selector ← Security.ChainMass.sampleSelector (singleShape h w v) hv hw
      let starts ← sampleStarts (singleShape h w v)
      let _ ← sampleUpperCoins (singleShape h w v) sample
      finish (chainPositionEquiv selector) (startsEquiv starts)) =ᵈ
    (do
      let selector ← ($ᵗ (GXMSS.Reductions.Guess h w v) : ProbComp _)
      let starts ← GXMSS.sampleStarts H h v
      finish selector starts) := by
  calc
    _ =ᵈ ((do
        let selector ← Security.ChainMass.sampleSelector (singleShape h w v) hv hw
        let starts ← GXMSS.sampleStarts H h v
        finish (chainPositionEquiv selector) starts) : ProbComp A) := by
      apply EvalDistEq.bind_right
      intro selector
      exact singleLayerStartDraws_evalDistEq sample (finish (chainPositionEquiv selector))
    _ =ᵈ _ := by
      simpa only [bind_map_left] using
        (sampleSelector_evalDistEq (h := h) (v := v) hv hw).bind_left
          (fun selector => GXMSS.sampleStarts H h v >>= finish selector)

private theorem singleLayerUDDraws_evalDistEq [SampleableType H]
    [NeZero v] [NeZero (2 ^ w - 1)] {A Coins : Type}
    (hv : 0 < v) (hw : 0 < w) (sample : ProbComp Coins)
    (finish : GXMSS.Reductions.Guess h w v → Fin (2 ^ w - 1) →
      (Fin (2 ^ h) → Fin v → H) → ProbComp A) :
    (do
      let selector ← Security.ChainMass.sampleSelector (singleShape h w v) hv hw
      let cut ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp _)
      let starts ← sampleStarts (singleShape h w v)
      let _ ← sampleUpperCoins (singleShape h w v) sample
      finish (chainPositionEquiv selector) cut (startsEquiv starts)) =ᵈ
    (do
      let selector ← ($ᵗ (GXMSS.Reductions.Guess h w v) : ProbComp _)
      let cut ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp _)
      let starts ← GXMSS.sampleStarts H h v
      finish selector cut starts) := by
  calc
    _ =ᵈ ((do
        let selector ← Security.ChainMass.sampleSelector (singleShape h w v) hv hw
        let cut ← ($ᵗ (Fin (2 ^ w - 1)) : ProbComp _)
        let starts ← GXMSS.sampleStarts H h v
        finish (chainPositionEquiv selector) cut starts) : ProbComp A) := by
      apply EvalDistEq.bind_right
      intro selector
      apply EvalDistEq.bind_right
      intro cut
      exact singleLayerStartDraws_evalDistEq sample (finish (chainPositionEquiv selector) cut)
    _ =ᵈ _ := by
      simpa only [bind_map_left] using
        (sampleSelector_evalDistEq (h := h) (v := v) hv hw).bind_left
          (fun selector => ($ᵗ (Fin (2 ^ w - 1)) : ProbComp _) >>= fun cut =>
            GXMSS.sampleStarts H h v >>= finish selector cut)

/-- A selected terminal extraction succeeds; every other branch retains the total fallback. -/
theorem invertAt_boolean_single [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sampling : RetrySampling R)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) (pp : PP)
    (selector : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → sampling.internal.Coins) :
    let ends := Security.ChainContinuation.spliceEndpoints (liftHash hash) pp selector.1
      selector.2.1 selector.2.2.val answer starts
    let metadata := Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
      sampling.internal pp ends upperCoins
    let references := Security.ChainContinuation.canonicalReferences metadata
      (Security.ChainContinuation.splicePrefixes (liftHash hash) pp selector.1 selector.2.1
        selector.2.2.val answer starts)
    let fallback := Security.canonicalPreimageFallback starts
      (by have := selector.2.1.isLt; omega)
    (fun preimage => decide (hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector))
        (hash.digestInput preimage) = answer)) <$>
      Security.invertAt (liftHash hash) (familyOfEncoding enc) sampling adv pp selector answer
        starts upperCoins =
      (fun out => decide (hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector))
          (hash.digestInput fallback) = answer) ||
        out.2.elim false (fun state => Security.selectedCutObservation (liftHash hash)
          (familyOfEncoding enc) pp selector answer ends metadata references out.1 state)) <$>
        Security.ChainMass.runFilteredRaw (liftHash hash) (familyOfEncoding enc) sampling adv
          pp selector.1 selector.2.1 (selector.2.2.val + 1) selector.2.2.val answer starts
          upperCoins := by
  dsimp only
  unfold Security.invertAt
  simp only [map_bind, map_pure, privateBad_single, Bool.false_eq_true, ↓reduceIte]
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨forgery, state⟩
  dsimp only [Function.comp_def]
  cases state with
  | none =>
    simp only [Option.elim_none, Bool.or_false]
    rfl
  | some state =>
    by_cases hselected : Security.selectedCutObservation (liftHash hash)
        (familyOfEncoding enc) pp selector answer
        (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp selector.1
          selector.2.1 selector.2.2.val answer starts)
        (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
          sampling.internal pp
          (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp selector.1
            selector.2.1 selector.2.2.val answer starts) upperCoins)
        (Security.ChainContinuation.canonicalReferences
          (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
            sampling.internal pp
            (Security.ChainContinuation.spliceEndpoints (liftHash hash) pp selector.1
              selector.2.1 selector.2.2.val answer starts) upperCoins)
          (Security.ChainContinuation.splicePrefixes (liftHash hash) pp selector.1
            selector.2.1 selector.2.2.val answer starts)) forgery state = true
    · obtain ⟨preimage, hextract, heval⟩ := Security.selectedCutObservation_sound
        (liftHash hash) (familyOfEncoding enc) pp selector answer _ _ _ forgery state hselected
      simp only [hselected, ↓reduceIte, hextract, Option.getD_some,
        Option.elim_some, Bool.or_true]
      congr 1
      apply decide_eq_true
      simpa [liftHash, chainPositionEquiv, otsEquiv] using heval
    · simp [hselected]
      rfl

private theorem jointPreimageWitness_boolean [NeZero v]
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) (pp : PP)
    (guess : GXMSS.Reductions.Guess h w v) (answer : H)
    (starts : Fin (2 ^ h) → Fin v → H) (out : GXMSS.Reductions.Result PP H M R h v)
    (hout : out ∈ support (GXMSS.Reductions.runSpliced hash enc K adv pp guess answer starts)) :
    decide (hash.thf.eval pp (hash.chainTweak guess)
      (hash.digestInput (GXMSS.Reductions.jointPreimageWitness hash enc K guess starts out)) =
        answer) =
      (decide (hash.thf.eval pp (hash.chainTweak guess)
        (hash.digestInput (starts 0 0)) = answer) ||
        GXMSS.Reductions.jointChainObservation hash enc K (guess, out)) := by
  by_cases hwin : GXMSS.Reductions.jointChainObservation hash enc K (guess, out) = true
  · have heval := GXMSS.Reductions.jointPreimageWitness_sound hash enc K adv pp guess answer
      starts out hout hwin
    simpa only [hwin, Bool.or_true, decide_eq_true_eq, GXMSS.Reductions.guessedEpoch,
      GXMSS.Reductions.guessedChain, GXMSS.Reductions.guessedPosition] using heval
  · simp [GXMSS.Reductions.jointPreimageWitness, hwin]

private theorem jointPRE_fixed_boolean_filtered [NeZero v]
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) (pp : PP)
    (guess : GXMSS.Reductions.Guess h w v) (answer : H)
    (starts : Fin (2 ^ h) → Fin v → H) :
    (fun out => decide (hash.thf.eval pp (hash.chainTweak guess)
      (hash.digestInput (GXMSS.Reductions.jointPreimageWitness hash enc K guess starts out)) =
        answer)) <$> GXMSS.Reductions.runSpliced hash enc K adv pp guess answer starts =ᵈ
    (fun out => decide (hash.thf.eval pp (hash.chainTweak guess)
        (hash.digestInput (starts 0 0)) = answer) ||
      out.elim false (fun result =>
        GXMSS.Reductions.jointChainObservation hash enc K (guess, result))) <$>
      GXMSS.Reductions.runFilteredSpliced hash enc K adv pp guess guess answer starts := by
  have hpoint : (fun out => decide (hash.thf.eval pp (hash.chainTweak guess)
      (hash.digestInput (GXMSS.Reductions.jointPreimageWitness hash enc K guess starts out)) =
        answer)) <$> GXMSS.Reductions.runSpliced hash enc K adv pp guess answer starts =ᵈ
      (fun out => decide (hash.thf.eval pp (hash.chainTweak guess)
          (hash.digestInput (starts 0 0)) = answer) ||
        GXMSS.Reductions.jointChainObservation hash enc K (guess, out)) <$>
        GXMSS.Reductions.runSpliced hash enc K adv pp guess answer starts := by
    simp only [map_eq_bind_pure_comp]
    apply EvalDistEq.bind_congr_of_support
    intro out hout
    dsimp only [Function.comp_def]
    rw [jointPreimageWitness_boolean hash enc K adv pp guess answer starts out hout]
  apply hpoint.trans
  by_cases hfall : hash.thf.eval pp (hash.chainTweak guess)
      (hash.digestInput (starts 0 0)) = answer
  · simp only [hfall, decide_true, Bool.true_or]
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      ((EvalDistEq.bind_const _ (pure true)).trans (EvalDistEq.bind_const _ (pure true)).symm)
  · simp only [hfall, decide_false, Bool.false_or]
    apply bool_evalDistEq_of_true
    exact GXMSS.Reductions.runSpliced_selectedMass_eq_filtered hash enc K adv pp guess guess
      answer starts

private theorem jointUDExperiment_filtered_evalDistEq
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw adv)
      =ᵈ GXMSS.Reductions.jointUDFilteredProgram hash enc K adv world := by
  rw [GXMSS.Reductions.jointUDExperiment_eq_explicit]
  apply bool_evalDistEq_of_true
  exact GXMSS.Reductions.jointUDExplicit_mass_eq_filtered hash enc K adv world

private theorem runObserved_iid_single [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (pp : PP) (selector splice : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins)
    (hselected : splice.1 = selector.1) (hchain : splice.2.1 = selector.2.1) :
    Security.ChainMass.runObserved (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) adv pp splice.1 splice.2.1 (selector.2.2.val + 1)
        splice.2.2.val answer starts upperCoins
        (Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc) pp selector) =ᵈ
    (fun out => out.elim false (fun result =>
      GXMSS.Reductions.jointChainObservation hash enc K (chainPositionEquiv selector, result))) <$>
      GXMSS.Reductions.runFilteredSpliced hash enc K (adversaryToOrdinary adv) pp
        (chainPositionEquiv selector) (chainPositionEquiv splice) answer (startsEquiv starts) := by
  let ends := Security.ChainContinuation.spliceEndpoints (liftHash hash) pp splice.1
    splice.2.1 splice.2.2.val answer starts
  have hraw := (runFilteredRaw_iid_single hash enc K J adv pp selector splice answer starts
    upperCoins hselected hchain).map
      (fun out => out.elim false (fun result =>
        GXMSS.Reductions.jointChainObservation hash enc K (chainPositionEquiv selector, result)))
  calc
    _ =ᵈ ((fun raw => (spliceResultObservation hash pp starts ends raw).elim false
        (fun result => GXMSS.Reductions.jointChainObservation hash enc K
          (chainPositionEquiv selector, result))) <$>
        Security.ChainMass.runFilteredRaw (liftHash hash) (familyOfEncoding enc)
          (RetrySampling.iid K J) adv pp splice.1 splice.2.1 (selector.2.2.val + 1)
            splice.2.2.val answer starts upperCoins : ProbComp Bool) := by
      unfold Security.ChainMass.runObserved
      simp only [privateBad_single, Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp]
      apply EvalDistEq.bind_congr_of_support
      rintro ⟨forgery, state⟩ hout
      dsimp only [Function.comp_def]
      cases state with
      | none => rfl
      | some state =>
        have hobs := selectedCutObservation_runFilteredRaw_single hash enc K J adv pp selector
          splice (selector.2.2.val + 1) answer starts upperCoins (forgery, some state) hout
          state rfl
        have heq := congrArg (pure : Bool → ProbComp Bool) hobs
        have hd := EvalDistEq.of_evalDist_eq
          (congrArg (fun computation : ProbComp Bool => 𝒟[computation]) heq)
        simpa only [spliceResultObservation, Option.map_some, Option.elim_some, ends,
          currentSpliceObservation, RetrySampling.iid, hselected, hchain] using hd
    _ =ᵈ _ := by simpa only [Functor.map_map] using hraw

private theorem invertAt_iid_single [SampleableType H] [SampleableType R] [NeZero v]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (pp : PP) (selector : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (upperCoins : UpperPosition (singleShape h w v) → (RetryPlan.iid R J).Coins) :
    (fun preimage => decide (hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector))
        (hash.digestInput preimage) = answer)) <$>
      Security.invertAt (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) adv pp
        selector answer starts upperCoins =ᵈ
    (fun out => decide (hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector))
      (hash.digestInput (GXMSS.Reductions.jointPreimageWitness hash enc K
        (chainPositionEquiv selector) (startsEquiv starts) out)) = answer)) <$>
      GXMSS.Reductions.runSpliced hash enc K (adversaryToOrdinary adv) pp
        (chainPositionEquiv selector) answer (startsEquiv starts) := by
  let fallbackWins := decide (hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector))
    (hash.digestInput (startsEquiv starts 0 0)) = answer)
  have hobs := (runObserved_iid_single hash enc K J adv pp selector selector answer starts
    upperCoins rfl rfl).map (fun win => fallbackWins || win)
  have hpre := jointPRE_fixed_boolean_filtered hash enc K (adversaryToOrdinary adv) pp
    (chainPositionEquiv selector) answer (startsEquiv starts)
  apply EvalDistEq.trans _ hpre.symm
  have hbool := invertAt_boolean_single hash enc (RetrySampling.iid K J) adv pp selector
    answer starts upperCoins
  dsimp only [RetrySampling.iid] at hbool ⊢
  rw [hbool]
  have hzero : (⟨0, NeZero.pos v⟩ : Fin v) = 0 := by
    apply Fin.ext
    simp
  simpa only [Security.ChainMass.runObserved,
    Security.ChainContinuation.splicePrefixes_selected_cut, privateBad_single,
    Bool.false_eq_true, ↓reduceIte, map_bind, map_pure, Functor.map_map,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, fallbackWins,
    canonicalPreimageFallback_single, hzero, RetrySampling.iid] using hobs

/-- The complete original-domain PRE experiment agrees at depth one, including invalid,
filtered and accidental canonical-fallback wins. -/
theorem chainPREExperiment_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_PRE_Experiment (Security.chainPreimageReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) hv hw adv) =ᵈ
    SM_DT_PRE_Experiment (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw
      (adversaryToOrdinary adv)) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (Nat.ne_of_gt hw); omega⟩
  rw [Security.chainPreimageReduction_experiment,
    GXMSS.Reductions.jointPREExperiment_eq_explicit]
  unfold Security.explicitPREProgram GXMSS.Reductions.jointPREExplicitProgram
  simp only [GXMSS.Reductions.guessedEpoch, GXMSS.Reductions.guessedChain,
    GXMSS.Reductions.guessedPosition]
  apply EvalDistEq.bind_right
  intro pp
  let finish : GXMSS.Reductions.Guess h w v → (Fin (2 ^ h) → Fin v → H) → ProbComp Bool :=
    fun guess starts => do
      let hidden ← ($ᵗ H : ProbComp H)
      let answer := hash.thf.eval pp (hash.chainTweak guess) (hash.digestInput hidden)
      let out ← GXMSS.Reductions.runSpliced hash enc K (adversaryToOrdinary adv) pp guess
        answer starts
      pure (decide (hash.thf.eval pp (hash.chainTweak guess)
        (hash.digestInput (GXMSS.Reductions.jointPreimageWitness hash enc K guess starts out)) =
          answer))
  have hdraw := singleLayerDraws_evalDistEq (H := H) (h := h) (w := w) (v := v) hv hw
    (RetrySampling.iid (R := R) K J).sampleInternal finish
  apply EvalDistEq.trans _ hdraw
  apply EvalDistEq.bind_right
  intro selector
  apply EvalDistEq.bind_right
  intro starts
  apply EvalDistEq.bind_right
  intro upperCoins
  apply EvalDistEq.bind_right
  intro hidden
  have heval (input : H) :
      (liftHash hash).thf.eval pp ((liftHash hash).chainTweak selector)
        ((liftHash hash).digestInput input) =
      hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector)) (hash.digestInput input) :=
    rfl
  simp only [heval]
  have hfixed := invertAt_iid_single hash enc K J adv pp selector
    (hash.thf.eval pp (hash.chainTweak (chainPositionEquiv selector)) (hash.digestInput hidden))
    starts upperCoins
  simpa only [map_eq_bind_pure_comp, Function.comp_def, chainPositionEquiv_apply] using hfixed

/-- Native and complete-tree one-target PRE advantages are exactly equal at depth one. -/
theorem chainPREAdvantage_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_PRE_Advantage (Security.chainPreimageReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) hv hw adv) =
    SM_DT_PRE_Advantage (GXMSS.Reductions.jointPreimageReduction hash enc K hv hw
      (adversaryToOrdinary adv)) := by
  unfold SM_DT_PRE_Advantage
  exact congrArg (fun measure : Measure Bool => measure {true})
    (chainPREExperiment_single hash enc K J hv hw adv).evalDist_eq

/-- Each authoritative UD world agrees with its complete-tree world at depth one. -/
theorem chainUDExperiment_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (Security.chainUndetectabilityReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) hv hw adv
      (Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc))) =ᵈ
    SM_DT_UD_Experiment world (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw
      (adversaryToOrdinary adv)) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (Nat.ne_of_gt hw); omega⟩
  apply EvalDistEq.trans _
    (jointUDExperiment_filtered_evalDistEq hash enc K hv hw (adversaryToOrdinary adv) world).symm
  rw [Security.chainUndetectabilityReduction_experiment]
  unfold Security.explicitUDProgram GXMSS.Reductions.jointUDFilteredProgram
  simp only [GXMSS.Reductions.guessedEpoch, GXMSS.Reductions.guessedChain,
    GXMSS.Reductions.guessedPosition]
  apply EvalDistEq.bind_right
  intro pp
  let finish : GXMSS.Reductions.Guess h w v → Fin (2 ^ w - 1) →
      (Fin (2 ^ h) → Fin v → H) → ProbComp Bool := fun selector cut starts => do
    let answer ← SM_DT_UD_response world (GXMSS.Reductions.chainUDProblem hash) pp
      (hash.chainTweak (selector.1, selector.2.1, cut))
    if cut.val < selector.2.2.val then
      let out ← GXMSS.Reductions.runFilteredSpliced hash enc K (adversaryToOrdinary adv) pp
        selector (selector.1, selector.2.1, cut) answer starts
      pure (out.elim false (fun result =>
        GXMSS.Reductions.jointChainObservation hash enc K (selector, result)))
    else pure false
  have hdraw := singleLayerUDDraws_evalDistEq (H := H) (h := h) (w := w) (v := v) hv hw
    (RetrySampling.iid (R := R) K J).sampleInternal finish
  apply EvalDistEq.trans _ hdraw
  apply EvalDistEq.bind_right
  intro selector
  apply EvalDistEq.bind_right
  intro cut
  apply EvalDistEq.bind_right
  intro starts
  apply EvalDistEq.bind_right
  intro upperCoins
  dsimp only [finish]
  rw [chainUD_response_single hash pp (selector.1, selector.2.1, cut) world]
  simp only [chainPositionEquiv_apply]
  apply EvalDistEq.bind_right
  intro answer
  by_cases hactive : cut.val < selector.2.2.val
  · simp only [hactive, ↓reduceIte]
    simpa only [map_eq_bind_pure_comp, Function.comp_def, chainPositionEquiv_apply] using
      runObserved_iid_single hash enc K J adv pp selector (selector.1, selector.2.1, cut)
        answer starts upperCoins rfl rfl
  · simp only [hactive, ↓reduceIte]
    exact EvalDistEq.refl _

/-- Both native UD worlds induce the identical complete-tree distinguishing advantage. -/
theorem chainUDAdvantage_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_UD_Advantage (Security.chainUndetectabilityReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) hv hw adv
      (Security.selectedCutObservation (liftHash hash) (familyOfEncoding enc))) =
    SM_DT_UD_Advantage (GXMSS.Reductions.jointUndetectabilityReduction hash enc K hv hw
      (adversaryToOrdinary adv)) := by
  unfold SM_DT_UD_Advantage
  rw [(chainUDExperiment_single hash enc K J hv hw adv .real).evalDist_eq,
    (chainUDExperiment_single hash enc K J hv hw adv .ideal).evalDist_eq]

end GXMSS.Hypertree.SingleLayer
