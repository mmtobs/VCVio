/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
public import HashSig.GXMSS.Security.Hypertree.Reductions.EncodingCollision
public import HashSig.GXMSS.Security.Reductions.Problems
import all HashSig.GXMSS.Hypertree.SingleLayer
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncoding
import all HashSig.GXMSS.Security.Reductions.EncodingCollision
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
import all HashSig.GXMSS.Security.Hypertree.Reductions.EncodingCollision
import all HashSig.GXMSS.Security.Auxiliary.Encoding

/-!
# Depth-one encoding-game transport

Complete-coordinate family queries become ordinary epoch/message queries. Optional selected
words, exhausted records, repeated requests and the total record cap retain their exact meaning.
The adaptive transport uses the actual IID finite-tape projection to recursive retry sampling.
-/

public section

namespace GXMSS.Hypertree.SingleLayer.EncodingTransport

open Encoding OracleComp OracleSpec
open GXMSS.Hypertree.Security

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The actual depth-one family problem has no internal registration slots. -/
@[expose] noncomputable def problem [SampleableType R] (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ) :
    FamilyEncoding.Problem PP M H R (singleShape h w v) :=
  Security.familyEncodingProblem (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) qs

/-- Observe the application message and unchanged bounded ordinary epoch. -/
@[expose] def queryObservation (q : FamilyEncoding.Query M H (singleShape h w v)) :
    M × Fin (2 ^ h) :=
  (messageEquiv q.1 q.2, otsEquiv q.1)

/-- The coordinate/message observation is injective across the complete dependent query domain. -/
theorem queryObservation_injective :
    Function.Injective (queryObservation (M := M) (H := H) (h := h) (w := w) (v := v)) := by
  rintro ⟨p, msg⟩ ⟨q, other⟩ heq
  have hepoch := congrArg (fun q : M × Fin (2 ^ h) => q.2) heq
  have hp : p = q := otsEquiv.injective hepoch
  subst q
  have hm : msg = other := (messageEquiv p).injective (congrArg Prod.fst heq)
  subst other
  rfl

/-- Every logged failure and successful word retains its message and ordinary epoch. -/
@[expose] def recordObservation (entry : FamilyEncoding.Record M H R (singleShape h w v)) :
    TargetCollisionResistance.Record M R (Fin (2 ^ h)) v (2 ^ w) :=
  ⟨otsEquiv entry.position, messageEquiv entry.position entry.message, entry.result⟩

/-- Observe the complete ordered consumed-coordinate transcript. -/
@[expose] def transcriptObservation
    (entries : FamilyEncoding.Transcript M H R (singleShape h w v)) :
    TargetCollisionResistance.Transcript M R (Fin (2 ^ h)) v (2 ^ w) :=
  entries.map recordObservation

/-- Candidate observation retains the exact application-message/randomizer pair. -/
@[expose] def candidateObservation (candidate : FamilyEncoding.Forgery M H R (singleShape h w v)) :
    M × R × Fin (2 ^ h) :=
  ((queryObservation candidate.query).1, candidate.randomizer, (queryObservation candidate.query).2)

/-- Used coordinates and used ordinary epochs coincide, even after exhausted requests. -/
theorem used_observation (entries : FamilyEncoding.Transcript M H R (singleShape h w v))
    (p : OTSPosition (singleShape h w v)) :
    TargetCollisionResistance.used (transcriptObservation entries) (otsEquiv p) =
      FamilyEncoding.used entries p := by
  simp only [TargetCollisionResistance.used, FamilyEncoding.used, transcriptObservation,
    List.any_map]
  congr 1
  funext entry
  change decide (otsEquiv entry.position = otsEquiv p) = decide (entry.position = p)
  exact decide_eq_decide.mpr otsEquiv.injective.eq_iff

/-- Rejection depends on the same cap and the same previously consumed coordinate. -/
theorem rejected_observation (cap : ℕ)
    (entries : FamilyEncoding.Transcript M H R (singleShape h w v))
    (p : OTSPosition (singleShape h w v)) :
    TargetCollisionResistance.rejected cap (transcriptObservation entries) (otsEquiv p) =
      FamilyEncoding.rejected cap entries p := by
  unfold TargetCollisionResistance.rejected FamilyEncoding.rejected
  rw [used_observation]
  simp only [transcriptObservation, List.length_map]

/-- A component's captured unit-local encoder is the original encoder at its ordinary epoch. -/
theorem run_component_eq [Finite R] (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : OTSPosition (singleShape h w v)) (pp : PP)
    (msg : Message (singleShape h w v) M H p) (K : ℕ) (coins : (RetryPlan.iid R K).Coins) :
    (RetryPlan.iid R K).run ((familyOfEncoding enc).component p) pp msg () coins =
      (RetryPlan.iid R K).run enc pp (messageEquiv p msg) (otsEquiv p) coins := by
  apply RetryPlan.run_eq_of_values_eq
  intro i
  rfl

/-- Actual IID local sampling preserves returned success and exhaustion at every full coordinate. -/
theorem sampleResult_evalDistEq [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (pp : PP) (q : FamilyEncoding.Query M H (singleShape h w v)) :
    FamilyEncoding.sampleResult (problem hash enc qs K J) pp q =ᵈ
      enc.retry ($ᵗ R) pp (queryObservation q).1 (queryObservation q).2 K := by
  have hlayer := layer_zero q.1.1
  simp only [FamilyEncoding.sampleResult, problem, Security.familyEncodingProblem, hlayer,
    ↓reduceIte,
    RetrySampling.iid, run_component_eq, queryObservation]
  exact RetryPlan.iid_run_output_evalDistEq_retry enc pp _ _ K

private def ordinaryOnFamilyOracle [SampleableType R]
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ) (pp : PP) :
    QueryImpl (FamilyEncoding.challengeSpec M H R (singleShape h w v))
      (StateT (FamilyEncoding.Transcript M H R (singleShape h w v)) ProbComp) := fun q state =>
  if FamilyEncoding.rejected qs state q.1 then pure (none, state)
  else do
    let answer ← enc.retry ($ᵗ R) pp (queryObservation q).1 (queryObservation q).2 K
    pure (answer, state ++ [(⟨q.1, q.2, answer⟩ :
        FamilyEncoding.Record M H R (singleShape h w v))])

/-- The actual challenge sampler and recursive ordinary retry have the same full transition law. -/
private theorem challengeOracle_evalDistEq [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (pp : PP) (q : FamilyEncoding.Query M H (singleShape h w v))
    (state : FamilyEncoding.Transcript M H R (singleShape h w v)) :
    (FamilyEncoding.challengeOracle (problem hash enc qs K J) pp q).run state =ᵈ
      (ordinaryOnFamilyOracle enc qs K pp q).run state := by
  change (FamilyEncoding.challengeOracle (problem hash enc qs K J) pp q).run state =ᵈ
    (if FamilyEncoding.rejected qs state q.1 then pure (none, state) else do
      let answer ← enc.retry ($ᵗ R) pp (queryObservation q).1 (queryObservation q).2 K
      pure (answer, state ++ [(⟨q.1, q.2, answer⟩ :
        FamilyEncoding.Record M H R (singleShape h w v))]))
  have hcap : (problem (H := H) hash enc qs K J).numRecords = qs := by
    simp [problem, Security.familyEncodingProblem, upperCount, singleShape]
  by_cases hr : FamilyEncoding.rejected qs state q.1 = true
  · rw [FamilyEncoding.challengeOracle_run_of_rejected _ _ _ _ (by simpa [hcap] using hr)]
    simp only [hr, ↓reduceIte]
    exact EvalDistEq.refl _
  · have hf : FamilyEncoding.rejected qs state q.1 = false := Bool.eq_false_iff.mpr hr
    rw [FamilyEncoding.challengeOracle_run_of_eligible _ _ _ _ (by simpa [hcap] using hf)]
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      (sampleResult_evalDistEq hash enc qs K J pp q).map
        (fun answer => (answer, state ++ [(⟨q.1, q.2, answer⟩ :
        FamilyEncoding.Record M H R (singleShape h w v))]))

/-- Forward ambient draws unchanged and reindex each full-coordinate challenge query. -/
@[expose] def queryBridge : QueryImpl
    (unifSpec + FamilyEncoding.challengeSpec M H R (singleShape h w v))
    (OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R
      (Fin (2 ^ h)) v (2 ^ w)))
  | .inl q => liftM ((unifSpec + TargetCollisionResistance.challengeSpec M R
      (Fin (2 ^ h)) v (2 ^ w)).query (.inl q))
  | .inr q => liftM ((unifSpec + TargetCollisionResistance.challengeSpec M R
      (Fin (2 ^ h)) v (2 ^ w)).query (.inr (queryObservation q)))

/-- Translate the actual adaptive strategy, including every exhausted or repeated request. -/
@[expose] def adversaryToOrdinary [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : FamilyEncoding.Adversary (problem (H := H) hash enc qs K J)) :
    TargetCollisionResistance.Adversary (GXMSS.Reductions.encodingTCRProblem hash enc qs K) where
  find pp := candidateObservation <$> simulateQ queryBridge (adv.find pp)

private def ordinaryOnFamilyOracles [SampleableType R]
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ) (pp : PP) :
    QueryImpl (unifSpec + FamilyEncoding.challengeSpec M H R (singleShape h w v))
      (StateT (FamilyEncoding.Transcript M H R (singleShape h w v)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (FamilyEncoding.Transcript M H R (singleShape h w v)) ProbComp) +
      ordinaryOnFamilyOracle (H := H) enc qs K pp

private theorem ordinaryOnFamilyOracle_projection [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ) (pp : PP)
    (q : FamilyEncoding.Query M H (singleShape h w v))
    (state : FamilyEncoding.Transcript M H R (singleShape h w v)) :
    Prod.map id transcriptObservation <$>
      (ordinaryOnFamilyOracle enc qs K pp q).run state =
        (TargetCollisionResistance.challengeOracle
          (GXMSS.Reductions.encodingTCRProblem hash enc qs K) pp (queryObservation q)).run
            (transcriptObservation state) := by
  change Prod.map id transcriptObservation <$>
    (if FamilyEncoding.rejected qs state q.1 then pure (none, state) else do
      let answer ← enc.retry ($ᵗ R) pp (queryObservation q).1 (queryObservation q).2 K
      pure (answer, state ++ [(⟨q.1, q.2, answer⟩ :
        FamilyEncoding.Record M H R (singleShape h w v))])) = _
  have hr := rejected_observation qs state q.1
  by_cases h : FamilyEncoding.rejected qs state q.1 = true
  · rw [TargetCollisionResistance.challengeOracle_run_of_rejected _ _ _ _ (by
      simpa only [GXMSS.Reductions.encodingTCRProblem, queryObservation] using hr.trans h)]
    simp [h]
  · have hf : FamilyEncoding.rejected qs state q.1 = false := Bool.eq_false_iff.mpr h
    rw [TargetCollisionResistance.challengeOracle_run_of_eligible _ _ _ _ (by
      simpa only [GXMSS.Reductions.encodingTCRProblem, queryObservation] using hr.trans hf)]
    simp only [hf, Bool.false_eq_true, ↓reduceIte,
      GXMSS.Reductions.encodingTCRProblem, map_bind, map_pure]
    apply congrArg (fun next => enc.retry ($ᵗ R) pp (queryObservation q).1
      (queryObservation q).2 K >>= next)
    funext answer
    simp [Prod.map, transcriptObservation, recordObservation, queryObservation]

private theorem ordinaryOnFamilyOracles_projection [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K : ℕ) (pp : PP)
    (q : (unifSpec + FamilyEncoding.challengeSpec M H R (singleShape h w v)).Domain)
    (state : FamilyEncoding.Transcript M H R (singleShape h w v)) :
    Prod.map id transcriptObservation <$>
      (ordinaryOnFamilyOracles enc qs K pp q).run state =
        (simulateQ (TargetCollisionResistance.oracles
          (GXMSS.Reductions.encodingTCRProblem hash enc qs K) pp) (queryBridge q)).run
            (transcriptObservation state) := by
  cases q with
  | inl uniform =>
      simp [ordinaryOnFamilyOracles, queryBridge, TargetCollisionResistance.oracles]
  | inr challenge =>
      simp only [ordinaryOnFamilyOracles, queryBridge, TargetCollisionResistance.oracles,
        QueryImpl.add_apply_inr, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map]
      exact ordinaryOnFamilyOracle_projection hash enc qs K pp challenge state

/-- The collision predicate observes the same coordinate, word and exact message/randomizer pair. -/
theorem valid_observation [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (pp : PP)
    (state : FamilyEncoding.Transcript M H R (singleShape h w v))
    (candidate : FamilyEncoding.Forgery M H R (singleShape h w v)) :
    FamilyEncoding.valid (familyOfEncoding enc) pp state candidate =
      TargetCollisionResistance.valid enc pp (transcriptObservation state)
        (candidateObservation candidate) := by
  classical
  simp only [FamilyEncoding.valid, TargetCollisionResistance.valid, familyOfEncoding_value,
    candidateObservation, queryObservation, transcriptObservation, List.any_map]
  simp only [otsEquiv, Equiv.coe_fn_mk]
  cases hv : enc.value pp (messageEquiv candidate.query.1 candidate.query.2)
    candidate.randomizer candidate.query.1.2 with
  | none => rfl
  | some word =>
      dsimp only
      apply congrArg (List.any state)
      funext entry
      dsimp only [Function.comp_apply, recordObservation]
      cases he : entry.result with
      | none => rfl
      | some pair =>
          rcases pair with ⟨target, r⟩
          dsimp only
          apply decide_eq_decide.mpr
          constructor
          · rintro ⟨hp, hw, hfresh⟩
            refine ⟨congrArg otsEquiv hp, hw, ?_⟩
            intro hpair
            apply hfresh
            apply Prod.ext
            · apply queryObservation_injective
              exact Prod.ext (congrArg (fun p : M × R => p.1) hpair)
                (congrArg otsEquiv hp)
            · exact congrArg (fun p : M × R => p.2) hpair
          · rintro ⟨hp, hw, hfresh⟩
            refine ⟨otsEquiv.injective hp, hw, ?_⟩
            intro hpair
            apply hfresh
            exact congrArg
              (fun p : FamilyEncoding.Query M H (singleShape h w v) × R =>
                (messageEquiv p.1.1 p.1.2, p.2)) hpair


/-- The complete adaptive challenge interaction preserves its full returned transcript law. -/
theorem run_projected_evalDistEq {A : Type} [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ) (pp : PP)
    (program : OracleComp (unifSpec + FamilyEncoding.challengeSpec M H R (singleShape h w v)) A)
    (state : FamilyEncoding.Transcript M H R (singleShape h w v)) :
    Prod.map id transcriptObservation <$>
      (simulateQ (FamilyEncoding.oracles (problem hash enc qs K J) pp) program).run state =ᵈ
        (simulateQ (TargetCollisionResistance.oracles
          (GXMSS.Reductions.encodingTCRProblem hash enc qs K) pp)
          (simulateQ queryBridge program)).run (transcriptObservation state) := by
  have hi : (simulateQ (FamilyEncoding.oracles (problem hash enc qs K J) pp) program).run
      state =ᵈ (simulateQ (ordinaryOnFamilyOracles enc qs K pp) program).run state := by
    apply evalDistEq_simulateQ_run
    intro q history
    cases q with
    | inl q => rfl
    | inr q =>
        simpa only [FamilyEncoding.oracles, ordinaryOnFamilyOracles, QueryImpl.add_apply_inr]
          using challengeOracle_evalDistEq hash enc qs K J pp q history
  have hp := map_run_simulateQ_eq_of_query_map_eq
    (ordinaryOnFamilyOracles enc qs K pp)
    (TargetCollisionResistance.oracles (GXMSS.Reductions.encodingTCRProblem hash enc qs K) pp
      ∘ₛ queryBridge) transcriptObservation
      (ordinaryOnFamilyOracles_projection hash enc qs K pp)
        program state
  apply (hi.map (Prod.map id transcriptObservation)).trans
  rw [hp, QueryImpl.simulateQ_compose]

/-- The actual adaptive family experiment is the ordinary encoding target-collision experiment
under explicit strategy translation, preserving both Boolean outcomes and missing mass. -/
theorem experiment_evalDistEq [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : FamilyEncoding.Adversary (problem (H := H) hash enc qs K J)) :
    FamilyEncoding.experiment adv =ᵈ
      TargetCollisionResistance.experiment (adversaryToOrdinary hash enc qs K J adv) := by
  simp only [FamilyEncoding.experiment, TargetCollisionResistance.experiment,
    adversaryToOrdinary, problem, Security.familyEncodingProblem,
    GXMSS.Reductions.encodingTCRProblem]
  apply EvalDistEq.bind_right
  intro pp
  have hr := (run_projected_evalDistEq hash enc qs K J pp (adv.find pp) []).map
    (fun result => TargetCollisionResistance.valid enc pp result.2
      (candidateObservation result.1))
  simp only [Functor.map_map, Prod.map, Function.id_def] at hr
  have hvalid : (fun result : FamilyEncoding.Forgery M H R (singleShape h w v) ×
      FamilyEncoding.Transcript M H R (singleShape h w v) =>
      TargetCollisionResistance.valid enc pp (transcriptObservation result.2)
        (candidateObservation result.1)) =
      (fun result => FamilyEncoding.valid (familyOfEncoding enc) pp result.2 result.1) := by
    funext result
    exact (valid_observation enc pp result.2 result.1).symm
  rw [hvalid] at hr
  simpa only [simulateQ_map, StateT.run_map, transcriptObservation, List.map_nil,
    bind_pure_comp, Functor.map_map, Function.comp_def,
    problem, Security.familyEncodingProblem, GXMSS.Reductions.encodingTCRProblem] using hr

/-- Full Boolean output measures agree for the two actual encoding games. -/
theorem outputMeasure_eq [SampleableType R] [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : FamilyEncoding.Adversary (problem (H := H) hash enc qs K J)) :
    FamilyEncoding.outputMeasure adv =
      TargetCollisionResistance.outputMeasure (adversaryToOrdinary hash enc qs K J adv) :=
  (experiment_evalDistEq hash enc qs K J adv).evalDist_eq

/-- The exact strategy-dependent family advantage becomes an ordinary encoding-game advantage. -/
theorem advantage_eq [SampleableType R] [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : FamilyEncoding.Adversary (problem (H := H) hash enc qs K J)) :
    FamilyEncoding.advantage adv =
      TargetCollisionResistance.advantage (adversaryToOrdinary hash enc qs K J adv) := by
  unfold FamilyEncoding.advantage TargetCollisionResistance.advantage
  rw [outputMeasure_eq hash enc qs K J adv]

/-- In particular, the actual hypertree encoding reduction has an exact ordinary encoding-game
experiment under this explicit family-query strategy translation. -/
theorem reduction_experiment_evalDistEq [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    FamilyEncoding.experiment (Security.encodingTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) qs adv) =ᵈ
        TargetCollisionResistance.experiment (adversaryToOrdinary hash enc qs K J
          (Security.encodingTargetCollisionReduction (liftHash hash) (familyOfEncoding enc)
            (RetrySampling.iid K J) qs adv)) :=
  experiment_evalDistEq hash enc qs K J _

/-- The named family reduction's advantage is exactly its ordinary translated game's advantage. -/
theorem reduction_advantage_eq [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    FamilyEncoding.advantage (Security.encodingTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) qs adv) =
        TargetCollisionResistance.advantage (adversaryToOrdinary hash enc qs K J
          (Security.encodingTargetCollisionReduction (liftHash hash) (familyOfEncoding enc)
            (RetrySampling.iid K J) qs adv)) :=
  advantage_eq hash enc qs K J _


/-- At depth one the complete candidate scan consists of the bottom candidate. -/
theorem selectEncodingCandidate_single [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (pp : PP)
    (ledger : FamilyEncoding.Transcript M H R (singleShape h w v))
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))) :
    selectEncodingCandidate (liftHash hash) (familyOfEncoding enc) pp ledger forgery =
      bottomEncodingCandidate forgery := by
  simp only [selectEncodingCandidate, encodingCandidates, singleShape, Nat.sub_self,
    List.ofFn_zero, List.filterMap_nil, List.find?_cons, List.find?_nil]
  split <;> rfl

/-- The selected candidate is the ordinary forgery's exact message, randomizer and epoch. -/
theorem candidateObservation_select [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (pp : PP)
    (ledger : FamilyEncoding.Transcript M H R (singleShape h w v))
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))) :
    candidateObservation
      (selectEncodingCandidate (liftHash hash) (familyOfEncoding enc) pp ledger forgery) =
        ((forgeryObservation forgery).2.1,
          (forgeryObservation forgery).2.2.randomizer, (forgeryObservation forgery).1) := by
  rw [selectEncodingCandidate_single]
  change (messageEquiv _ (bottomMessage forgery.1 forgery.2.1), _, _) = _
  rw [messageEquiv_bottomMessage]
  simp [bottomEncodingCandidate, queryObservation, forgeryObservation, signatureEquiv_apply]

/-- Signature materialization observes exactly the ordinary signature, including exhaustion. -/
theorem signFromResults_single (hash : GXMSS.HashInstance PP T X H h w v)
    (sk : SecretKey PP H Unit (singleShape h w v))
    (upper : UpperPosition (singleShape h w v) → Option (Codeword v (2 ^ w) × R))
    (ep : Epoch (singleShape h w v)) (answer : Option (Codeword v (2 ^ w) × R)) :
    signFromResults (liftHash hash) sk upper ep answer =
      Option.map signatureEquiv.symm
        (answer.map (GXMSS.signatureOfWord hash (secretKeyEquiv Unit sk) (epochEquiv ep))) := by
  cases answer with
  | none => rfl
  | some wr =>
    simp [signFromResults, componentSignature_eq, otsEquiv_bottomPosition, signatureEquiv,
      singleShape]

/-- Observe the complete private encoding state, retaining failed records and their order. -/
@[expose] def stateObservation (state : EncodingReductionState M H R (singleShape h w v)) :=
  (historyObservation state.1, transcriptObservation state.2)

private def recursiveSourceOracles [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : SecretKey PP H Unit (singleShape h w v))
    (upper : UpperPosition (singleShape h w v) → Option (Codeword v (2 ^ w) × R)) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (EncodingReductionState M H R (singleShape h w v)) ProbComp) +
    encodingSigningOracleWith (fun q => enc.retry ($ᵗ R) sk.seed
      (queryObservation q).1 (queryObservation q).2 K) (liftHash hash) sk upper

private theorem recursiveSourceOracles_projection [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : SecretKey PP H Unit (singleShape h w v))
    (upper : UpperPosition (singleShape h w v) → Option (Codeword v (2 ^ w) × R))
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))).Domain)
    (state : EncodingReductionState M H R (singleShape h w v)) :
    Prod.map id stateObservation <$>
      (recursiveSourceOracles hash enc K sk upper q).run state =
      (simulateQ (GXMSS.Reductions.encodingSourceCoupledImpl hash enc K (secretKeyEquiv Unit sk))
        (SingleLayer.queryBridge q)).run (stateObservation state) := by
  cases q with
  | inl uniform =>
    simp only [recursiveSourceOracles, SingleLayer.queryBridge, QueryImpl.add_apply_inl,
      simulateQ_spec_query]
    rfl
  | inr request =>
    rcases request with ⟨ep, msg⟩
    simp only [recursiveSourceOracles, QueryImpl.add_apply_inr, SingleLayer.queryBridge,
      simulateQ_map, StateT.run_map, simulateQ_spec_query]
    unfold StateT.run GXMSS.Reductions.encodingSourceCoupledImpl encodingSigningOracleWith
    dsimp only [stateObservation, secretKeyEquiv_seed]
    cases hh : state.1 ep with
    | some entry => simp [historyObservation, hh, stateObservation]
    | none =>
      simp only [historyObservation, Equiv.symm_apply_apply, hh, Option.map_none,
        map_bind, map_pure, signFromResults_single, queryObservation,
        messageEquiv_bottomMessage, otsEquiv_bottomPosition]
      apply bind_congr
      intro answer
      simp [Prod.map, stateObservation, historyObservation_update, transcriptObservation,
        recordObservation, Option.map_map, Function.comp_def, messageEquiv_bottomMessage]

private theorem sourceEncodingSigningOracles_evalDistEq [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (sk : SecretKey PP H Unit (singleShape h w v))
    (upper : UpperPosition (singleShape h w v) → Option (Codeword v (2 ^ w) × R))
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))).Domain)
    (state : EncodingReductionState M H R (singleShape h w v)) :
    (sourceEncodingSigningOracles
      (familyEncodingProblem (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) qs)
        sk.seed (liftHash hash) sk upper q).run state =ᵈ
      (recursiveSourceOracles hash enc K sk upper q).run state := by
  cases q with
  | inl uniform => rfl
  | inr request =>
    rcases request with ⟨ep, msg⟩
    simp only [sourceEncodingSigningOracles, recursiveSourceOracles, QueryImpl.add_apply_inr]
    unfold StateT.run encodingSigningOracleWith
    cases hh : state.1 ep with
    | some entry => rfl
    | none =>
      simp only
      exact (sampleResult_evalDistEq hash enc qs K J sk.seed
        ⟨bottomPosition _ ep, bottomMessage ep msg⟩).bind fun answer => EvalDistEq.refl _

/-- The full encoding-result interaction retains precisely the historical consumed history and
ordered encoding transcript under IID sampling. All returned failures remain in both states. -/
private theorem source_run_projected_evalDistEq {A : Type} [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (sk : SecretKey PP H Unit (singleShape h w v))
    (upper : UpperPosition (singleShape h w v) → Option (Codeword v (2 ^ w) × R))
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) A)
    (state : EncodingReductionState M H R (singleShape h w v)) :
    Prod.map id stateObservation <$>
      (simulateQ (sourceEncodingSigningOracles
        (familyEncodingProblem (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) qs)
          sk.seed (liftHash hash) sk upper) program).run state =ᵈ
      (simulateQ (GXMSS.Reductions.encodingSourceCoupledImpl hash enc K (secretKeyEquiv Unit sk))
        (simulateQ SingleLayer.queryBridge program)).run (stateObservation state) := by
  have hi : (simulateQ (sourceEncodingSigningOracles
      (familyEncodingProblem (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) qs)
        sk.seed (liftHash hash) sk upper) program).run state =ᵈ
      (simulateQ (recursiveSourceOracles hash enc K sk upper) program).run state := by
    apply evalDistEq_simulateQ_run
    exact sourceEncodingSigningOracles_evalDistEq hash enc qs K J sk upper
  have hp := map_run_simulateQ_eq_of_query_map_eq
    (recursiveSourceOracles hash enc K sk upper)
    (GXMSS.Reductions.encodingSourceCoupledImpl hash enc K (secretKeyEquiv Unit sk)
      ∘ₛ SingleLayer.queryBridge) stateObservation
    (recursiveSourceOracles_projection hash enc K sk upper) program state
  apply (hi.map (Prod.map id stateObservation)).trans
  rw [hp, QueryImpl.simulateQ_compose]

private theorem encodingReplayWithKeys_single [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H Unit (singleShape h w v))
    (upper : UpperPosition (singleShape h w v) → Option (Codeword v (2 ^ w) × R)) :
    encodingReplayWithKeys (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      qs adv pk sk upper =ᵈ
      (do
        let result ← (simulateQ (GXMSS.Reductions.encodingSourceCoupledImpl hash enc K
          (secretKeyEquiv Unit sk)) ((SingleLayer.adversaryToOrdinary adv).forge pk)).run
            (SyncSignatureUnforgeability.emptyHistory, [])
        pure (TargetCollisionResistance.valid enc pk.seed result.2.2
          (result.1.2.1, result.1.2.2.randomizer, result.1.1))) := by
  have hp := (source_run_projected_evalDistEq hash enc qs K J sk upper (adv.forge pk)
    (SyncSignatureUnforgeability.emptyHistory, [])).map
      (fun result => TargetCollisionResistance.valid enc pk.seed result.2.2
        (candidateObservation (bottomEncodingCandidate result.1)))
  have hvalid : (fun result : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)) × EncodingReductionState M H R (singleShape h w v) =>
      TargetCollisionResistance.valid enc pk.seed (transcriptObservation result.2.2)
        (candidateObservation (bottomEncodingCandidate result.1))) =
      (fun result => FamilyEncoding.valid (familyOfEncoding enc) pk.seed result.2.2
        (selectEncodingCandidate (liftHash hash) (familyOfEncoding enc) pk.seed result.2.2
          result.1)) := by
    funext result
    rw [selectEncodingCandidate_single]
    exact (valid_observation enc pk.seed result.2.2 (bottomEncodingCandidate result.1)).symm
  simp only [Functor.map_map, Prod.map, Function.id_def, stateObservation] at hp
  rw [hvalid] at hp
  have hledger : upperLedgerFromResults (M := M) (liftHash hash) sk upper = [] :=
    List.length_eq_zero_iff.mp (by simp)
  simp only [SingleLayer.adversaryToOrdinary, simulateQ_map, StateT.run_map, bind_map_left]
  have hc : ∀ forgery : SyncSignatureUnforgeability.Forgery (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v)),
      candidateObservation (bottomEncodingCandidate forgery) =
        ((forgeryObservation forgery).2.1, (forgeryObservation forgery).2.2.randomizer,
          (forgeryObservation forgery).1) := by
    intro forgery
    rw [← selectEncodingCandidate_single hash enc pk.seed [] forgery]
    exact candidateObservation_select hash enc pk.seed [] forgery
  have hempty : historyObservation
      (SyncSignatureUnforgeability.emptyHistory : SyncSignatureUnforgeability.History
        (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) =
      SyncSignatureUnforgeability.emptyHistory := by
    funext ep
    rfl
  simpa only [encodingReplayWithKeys, hledger, stateObservation, hempty,
    transcriptObservation, List.map_nil, hc, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind] using hp

private def ordinaryReplayWithKeys [SampleableType R] [DecidableEq M] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v) : ProbComp Bool := do
  let result ← (simulateQ (GXMSS.Reductions.encodingSourceCoupledImpl hash enc K sk)
    (adv.forge pk)).run (SyncSignatureUnforgeability.emptyHistory, [])
  pure (TargetCollisionResistance.valid enc pk.seed result.2.2
    (result.1.2.1, result.1.2.2.randomizer, result.1.1))

private theorem encodingReplay_single [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    encodingReplay (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) qs adv =ᵈ
      (GXMSS.Reductions.encodingSourceCoupledProgram hash enc K
        (SingleLayer.adversaryToOrdinary adv) >>=
          GXMSS.Reductions.encodingTargetTail hash enc qs K) := by
  simp only [encodingReplay, GXMSS.Reductions.encodingSourceCoupledProgram,
    GXMSS.Reductions.encodingTargetTail, GXMSS.Reductions.encodingFinalFind,
    simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc]
  apply EvalDistEq.bind_right
  intro pp
  have hs := (sampleStarts_evalDistEq (H := H) (h := h) (w := w) (v := v)).bind_left
    (fun starts => ordinaryReplayWithKeys hash enc K (SingleLayer.adversaryToOrdinary adv)
      (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2)
  apply EvalDistEq.trans _ hs
  simp only [bind_map_left]
  apply EvalDistEq.bind_right
  intro starts
  apply EvalDistEq.trans _ (OracleComp.EvalDistEq.bind_const
    (sampleUpperResults (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid (R := R) K J).internal
      pp starts (RetrySampling.iid (R := R) K J).sampleInternal)
    (ordinaryReplayWithKeys hash enc K (SingleLayer.adversaryToOrdinary adv)
      (GXMSS.keys hash pp (startsEquiv starts)).1 (GXMSS.keys hash pp (startsEquiv starts)).2))
  apply EvalDistEq.bind_right
  intro upper
  simpa only [ordinaryReplayWithKeys, keys_public_eq, keys_secret_eq, ← startsEquiv_apply] using
    encodingReplayWithKeys_single hash enc qs K J adv
      (keys (liftHash hash) pp starts (fun _ => ())).1
      (keys (liftHash hash) pp starts (fun _ => ())).2 (fun p => (upper p).output)

/-- The ordinary signing adapter preserves the all-request signing-query budget. -/
theorem adversaryToOrdinary_queryBound
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) (qs : ℕ)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs)
    (pk : GXMSS.PublicKey PP H) :
    ((SingleLayer.adversaryToOrdinary adv).forge pk).IsQueryBoundP
      (fun q => q.isRight = true) qs := by
  rw [SingleLayer.adversaryToOrdinary, isQueryBoundP_map_iff]
  apply (hqueries pk).simulateQ_of_step
  · intro q hq
    cases q with
    | inl uniform => simp at hq
    | inr request => simp [SingleLayer.queryBridge]
  · intro q hq
    cases q with
    | inl uniform => simp [SingleLayer.queryBridge]
    | inr request => simp at hq

/-- The actual named depth-one family reduction and historical named ordinary reduction have
identical complete Boolean experiment laws, including missing mass and returned failures. -/
theorem historical_reduction_experiment_evalDistEq [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    FamilyEncoding.experiment (Security.encodingTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) qs adv) =ᵈ
      TargetCollisionResistance.experiment (GXMSS.Reductions.encodingTargetCollisionReduction
        hash enc qs K (SingleLayer.adversaryToOrdinary adv)) := by
  rw [familyExperiment_eq_encodingReplay _ _ _ _ _ hqueries,
    GXMSS.Reductions.encodingTargetExperiment_eq_coupled hash enc qs K
      (SingleLayer.adversaryToOrdinary adv) (adversaryToOrdinary_queryBound adv qs hqueries)]
  exact encodingReplay_single hash enc qs K J adv

/-- Complete named encoding experiment transport gives exact strategy-dependent advantage. -/
theorem historical_reduction_advantage_eq [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    FamilyEncoding.advantage (Security.encodingTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) qs adv) =
      TargetCollisionResistance.advantage (GXMSS.Reductions.encodingTargetCollisionReduction
        hash enc qs K (SingleLayer.adversaryToOrdinary adv)) := by
  exact congrArg (fun measure : MeasureTheory.Measure Bool => measure {true})
    (historical_reduction_experiment_evalDistEq hash enc qs K J adv hqueries).evalDist_eq

end GXMSS.Hypertree.SingleLayer.EncodingTransport
