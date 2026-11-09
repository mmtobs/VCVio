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
experiment under this explicit strategy translation. Historical simulators are separate. -/
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


end GXMSS.Hypertree.SingleLayer.EncodingTransport
