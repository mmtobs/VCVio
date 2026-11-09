/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncoding
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.HashRetry
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

/-!
# Mixed-coordinate accepted-output hash transport

The native hash challenge tests a coordinate-dependent acceptance predicate along each actual
captured retry plan and returns the first accepted randomizer. Messages inhabit their coordinate's
bottom or internal fibre. Failed eligible requests still consume their complete coordinate.

This strategy-indexed hash experiment is distinct from IID SM-DT-rTCR: its bottom and internal
coin samplers can generate correlated modular-counter sequences. No bound by the IID primitive is
asserted. The source client obtains its decoded word through public hash evaluation. The complete
adaptive simulation preserves both returned failure and unreturned mass.
-/

public section

namespace GXMSS.Hypertree.Security.FamilyEncodingAcceptedOutput

open Encoding Encoding.IncomparableEncoding OracleComp OracleSpec
open scoped ENNReal

variable {PP M H R Y : Type} {S : Shape}

/-- A hash family with distinct full-coordinate addresses represented by the query's dependent
coordinate, and public fibre-specific acceptance and decoding observations. -/
structure HashFamily (PP M H R Y : Type) (S : Shape) where
  /-- Full hash output at the complete coordinate and a message in its actual fibre. -/
  eval : PP → FamilyEncoding.Query M H S → R → Y
  /-- Acceptance can depend on the full coordinate. -/
  accepts : OTSPosition S → Y → Bool
  /-- Public decoding into the full word at that coordinate. -/
  word : OTSPosition S → Y → Codeword S.v (2 ^ S.w)

/-- Native strategy-indexed hash problem, with actual bottom/internal retry samplers. -/
structure Problem (PP M H R Y : Type) (S : Shape) where
  /-- Native hash and its public acceptance/decoding observations. -/
  hash : HashFamily PP M H R Y S
  /-- Captured plans and coin distributions; no IID premise. -/
  sampling : RetrySampling R
  /-- Common public-parameter sampler. -/
  paramGen : ProbComp PP
  /-- Total eligible-record capacity, including exhausted requests. -/
  numRecords : ℕ

/-- Native consumed-coordinate record. The optional randomizer is the original rTCR observation. -/
structure Record (M H R : Type) (S : Shape) where
  /-- Complete consumed coordinate. -/
  position : OTSPosition S
  /-- First message at that coordinate. -/
  message : Message S M H position
  /-- First accepted randomizer, or returned exhaustion. -/
  result : Option R

/-- Native hash history retains exhausted requests in issue order. -/
abbrev Transcript (M H R : Type) (S : Shape) := List (Record M H R S)

/-- The hash challenger exposes the first accepted randomizer, with public evaluation available. -/
abbrev challengeSpec (M H R : Type) (S : Shape) : OracleSpec (FamilyEncoding.Query M H S) :=
  (FamilyEncoding.Query M H S) →ₒ Option R

/-- Complete native search with fixed coins and metadata, for either configured retry plan. -/
@[expose] def fullResult (hash : HashFamily PP M H R Y S) (plan : RetryPlan R)
    (pp : PP) (q : FamilyEncoding.Query M H S) (coins : plan.Coins) : HashRetry.Result R :=
  HashRetry.search (fun r => hash.accepts q.1 (hash.eval pp q r)) plan.budget
    (plan.randomizers coins)

/-- Sample the actual finite coin value, then return the native first accepted randomizer. -/
@[expose] def sampleResult (prob : Problem PP M H R Y S) (pp : PP)
    (q : FamilyEncoding.Query M H S) : ProbComp (Option R) :=
  if q.1.1.1.val = 0 then
    (fun coins => (fullResult prob.hash prob.sampling.bottom pp q coins).output) <$>
      prob.sampling.sampleBottom
  else
    (fun coins => (fullResult prob.hash prob.sampling.internal pp q coins).output) <$>
      prob.sampling.sampleInternal

/-- Every returned native randomizer passes the actual coordinate's hash acceptance test. -/
theorem accepts_of_mem_sampleResult (prob : Problem PP M H R Y S) (pp : PP)
    (q : FamilyEncoding.Query M H S) {r : R}
    (h : some r ∈ support (sampleResult prob pp q)) :
    prob.hash.accepts q.1 (prob.hash.eval pp q r) = true := by
  unfold sampleResult at h
  split_ifs at h
  all_goals
    obtain ⟨coins, _, hcoins⟩ := OracleComp.mem_support_map_peel _ _ h
    exact HashRetry.accepts_of_search_output
      (fun r => prob.hash.accepts q.1 (prob.hash.eval pp q r)) _ _ hcoins.symm

/-- Publicly decode a native selected randomizer into the source client's observation. -/
@[expose] def decodeAnswer (hash : HashFamily PP M H R Y S) (pp : PP)
    (q : FamilyEncoding.Query M H S) (answer : Option R) :
    Option (Codeword S.v (2 ^ S.w) × R) :=
  answer.map fun r => (hash.word q.1 (hash.eval pp q r), r)

/-- Decode one native record while retaining its complete coordinate and dependent message. -/
@[expose] def decodeRecord (hash : HashFamily PP M H R Y S) (pp : PP)
    (entry : Record M H R S) : FamilyEncoding.Record M H R S :=
  ⟨entry.position, entry.message,
    decodeAnswer hash pp ⟨entry.position, entry.message⟩ entry.result⟩

/-- Project the entire native history, retaining all returned exhaustion slots. -/
@[expose] def decodeTranscript (hash : HashFamily PP M H R Y S) (pp : PP)
    (transcript : Transcript M H R S) : FamilyEncoding.Transcript M H R S :=
  transcript.map (decodeRecord hash pp)

/-- The native reservation test depends only on full coordinates and the total record cap. -/
@[expose] def rejected (cap : ℕ) (transcript : Transcript M H R S)
    (position : OTSPosition S) : Bool :=
  decide (cap ≤ transcript.length) || transcript.any fun entry => decide (entry.position = position)

/-- Native rejection reserves no new coordinate and draws no coins. Every eligible return,
including exhaustion, appends exactly one consumed-coordinate record. -/
@[expose] def challengeOracle (prob : Problem PP M H R Y S) (pp : PP) :
    QueryImpl (challengeSpec M H R S) (StateT (Transcript M H R S) ProbComp) := fun q => do
  let transcript ← get
  if rejected prob.numRecords transcript q.1 then return none
  else
    let answer ← (sampleResult prob pp q : StateT (Transcript M H R S) ProbComp _)
    set (transcript ++ [⟨q.1, q.2, answer⟩])
    return answer

/-- Rejection draws no retry coins and retains the entire native consumed-coordinate history. -/
theorem challengeOracle_run_of_rejected (prob : Problem PP M H R Y S) (pp : PP)
    (q : FamilyEncoding.Query M H S) (transcript : Transcript M H R S)
    (h : rejected prob.numRecords transcript q.1 = true) :
    (challengeOracle prob pp q).run transcript = pure (none, transcript) := by
  simp [challengeOracle, h]

/-- Every eligible native return appends exactly one record, including returned exhaustion. -/
theorem challengeOracle_run_of_eligible (prob : Problem PP M H R Y S) (pp : PP)
    (q : FamilyEncoding.Query M H S) (transcript : Transcript M H R S)
    (h : rejected prob.numRecords transcript q.1 = false) :
    (challengeOracle prob pp q).run transcript =
      (fun answer => (answer, transcript ++ [⟨q.1, q.2, answer⟩])) <$>
        sampleResult prob pp q := by
  simp [challengeOracle, h, map_eq_bind_pure_comp]

/-- Ambient randomness passes through unchanged. -/
@[expose] def oracles (prob : Problem PP M H R Y S) (pp : PP) :
    QueryImpl (unifSpec + challengeSpec M H R S) (StateT (Transcript M H R S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Transcript M H R S) ProbComp) +
    challengeOracle prob pp

/-- Native hash adversary using the complete-coordinate challenge API. -/
structure Adversary (prob : Problem PP M H R Y S) where
  /-- Adaptive candidate based on public evaluation and selected randomizers or exhaustion. -/
  find : PP → OracleComp (unifSpec + challengeSpec M H R S) (FamilyEncoding.Forgery M H R S)

/-- Same-coordinate full-hash collision at a successful target and a distinct query/randomizer
pair. Acceptance of the candidate is explicit; complete digests are compared. -/
@[expose] def valid [DecidableEq M] [DecidableEq H] [DecidableEq R] [DecidableEq Y]
    (hash : HashFamily PP M H R Y S) (pp : PP) (transcript : Transcript M H R S)
    (candidate : FamilyEncoding.Forgery M H R S) : Bool :=
  hash.accepts candidate.query.1 (hash.eval pp candidate.query candidate.randomizer) &&
    transcript.any fun entry => match entry.result with
      | none => false
      | some r => decide (entry.position = candidate.query.1 ∧
          hash.eval pp ⟨entry.position, entry.message⟩ r =
            hash.eval pp candidate.query candidate.randomizer ∧
          ((⟨entry.position, entry.message⟩ : FamilyEncoding.Query M H S), r) ≠
            (candidate.query, candidate.randomizer))

/-- Complete native experiment under the captured seed, coin laws and record capacity. -/
@[expose] def experiment [DecidableEq M] [DecidableEq H] [DecidableEq R] [DecidableEq Y]
    {prob : Problem PP M H R Y S} (adv : Adversary prob) : ProbComp Bool := do
  let pp ← prob.paramGen
  let (candidate, transcript) ← (simulateQ (oracles prob pp) (adv.find pp)).run []
  return valid prob.hash pp transcript candidate

/-- Native returned winning mass; neither exhaustion nor missing mass is conditioned away. -/
@[expose] noncomputable def advantage
    [DecidableEq M] [DecidableEq H] [DecidableEq R] [DecidableEq Y]
    {prob : Problem PP M H R Y S} (adv : Adversary prob) : ℝ≥0∞ :=
  𝒟[experiment adv] {true}

/-- The accepted-output bridge is fibrewise. It imposes no relation between incomparable codes
or decoder outputs at different coordinates. -/
structure AcceptedBridge (PP M H R Y : Type) (S : Shape) where
  /-- The native strategy-indexed hash problem. -/
  problem : Problem PP M H R Y S
  /-- The actual coordinate-indexed encoding family. -/
  family : EncodingFamily PP M R H S
  /-- Full decoding is injective only where this coordinate's hash acceptance succeeds. -/
  word_injOn : ∀ p, Set.InjOn (problem.hash.word p) {y | problem.hash.accepts p y = true}
  /-- The complete optional encoder observation, including returned failure. -/
  value_eq : ∀ pp q r, family.value q.1 pp q.2 r =
    if problem.hash.accepts q.1 (problem.hash.eval pp q r) then
      some (problem.hash.word q.1 (problem.hash.eval pp q r)) else none

namespace AcceptedBridge

/-- Source family problem with exactly the native seed, plans, coin laws and capacity. -/
@[expose] def encodingProblem (bridge : AcceptedBridge PP M H R Y S) :
    FamilyEncoding.Problem PP M H R S where
  family := bridge.family
  sampling := bridge.problem.sampling
  paramGen := bridge.problem.paramGen
  numRecords := bridge.problem.numRecords

/-- Each successful source equation establishes acceptance and the full-word observation. -/
theorem accepted_of_value_eq_some (bridge : AcceptedBridge PP M H R Y S) (pp : PP)
    (q : FamilyEncoding.Query M H S) (r : R) (word : Codeword S.v (2 ^ S.w))
    (hvalue : bridge.family.value q.1 pp q.2 r = some word) :
    bridge.problem.hash.accepts q.1 (bridge.problem.hash.eval pp q r) = true ∧
      word = bridge.problem.hash.word q.1 (bridge.problem.hash.eval pp q r) := by
  rw [bridge.value_eq] at hvalue
  split_ifs at hvalue with ha
  exact ⟨ha, Option.some.inj hvalue.symm⟩

/-- Full fixed-coin transport precedes all output projection. The selected attempt and consumed
prefix therefore agree for arbitrary correlated counter sequences as well as IID plans. -/
theorem fullResult_eq (bridge : AcceptedBridge PP M H R Y S) (plan : RetryPlan R)
    (pp : PP) (q : FamilyEncoding.Query M H S) (coins : plan.Coins) :
    plan.run (bridge.family.component q.1) pp q.2 () coins =
      (fullResult bridge.problem.hash plan pp q coins).toEncoding
        (fun r => bridge.problem.hash.word q.1 (bridge.problem.hash.eval pp q r)) := by
  exact HashRetry.run_eq_search plan (bridge.family.component q.1) pp q.2 ()
    (fun r => bridge.problem.hash.accepts q.1 (bridge.problem.hash.eval pp q r))
    (fun r => bridge.problem.hash.word q.1 (bridge.problem.hash.eval pp q r))
    (fun r => bridge.value_eq pp q r) coins

/-- The native full result satisfies the existing encoding first-success specification after
public decoding, including zero-based selection, one-based attempt and exact consumption. -/
theorem fullResult_isFirstSuccess (bridge : AcceptedBridge PP M H R Y S) (plan : RetryPlan R)
    (pp : PP) (q : FamilyEncoding.Query M H S) (coins : plan.Coins) :
    RetryPlan.IsFirstSuccess (bridge.family.component q.1) pp q.2 () (plan.randomizers coins)
      ((fullResult bridge.problem.hash plan pp q coins).toEncoding
        (fun r => bridge.problem.hash.word q.1 (bridge.problem.hash.eval pp q r))) := by
  rw [← bridge.fullResult_eq]
  exact plan.run_isFirstSuccess (bridge.family.component q.1) pp q.2 () coins

/-- Native selected-randomizer sampling decodes to the exact source optional output law. -/
theorem sampleResult_decode (bridge : AcceptedBridge PP M H R Y S) (pp : PP)
    (q : FamilyEncoding.Query M H S) :
    decodeAnswer bridge.problem.hash pp q <$> sampleResult bridge.problem pp q =
      FamilyEncoding.sampleResult bridge.encodingProblem pp q := by
  simp only [sampleResult, FamilyEncoding.sampleResult, encodingProblem]
  split_ifs <;> simp only [Functor.map_map]
  all_goals
    congr 1
    funext coins
    rw [bridge.fullResult_eq]
    exact (HashRetry.Result.output_toEncoding _ _).symm

/-- Native and source reservation tests use exactly the same occupied complete coordinates. -/
theorem rejected_decodeTranscript (bridge : AcceptedBridge PP M H R Y S) (pp : PP)
    (transcript : Transcript M H R S) (position : OTSPosition S) :
    FamilyEncoding.rejected bridge.problem.numRecords
        (decodeTranscript bridge.problem.hash pp transcript) position =
      rejected bridge.problem.numRecords transcript position := by
  simp only [FamilyEncoding.rejected, FamilyEncoding.used, rejected, decodeTranscript,
    List.length_map, List.any_map, Function.comp_def, decodeRecord]
  rfl

/-- The named reduction uses native accepted randomizers and publicly decodes the word expected
by the source adversary. It keeps the exact dependent query and candidate pair. -/
@[expose] def liftedOracles (bridge : AcceptedBridge PP M H R Y S) (pp : PP) :
    QueryImpl (unifSpec + FamilyEncoding.challengeSpec M H R S)
      (OracleComp (unifSpec + challengeSpec M H R S)) :=
  fun q => match q with
    | .inl random => (unifSpec + challengeSpec M H R S).query (.inl random)
    | .inr query => decodeAnswer bridge.problem.hash pp query <$>
        ((unifSpec + challengeSpec M H R S).query (.inr query) :
          OracleComp (unifSpec + challengeSpec M H R S) (Option R))

/-- Each translated native call agrees with the source call on the answer and full decoded
history. Rejection occurs before sampling in both handlers. -/
theorem oracles_decode (bridge : AcceptedBridge PP M H R Y S) (pp : PP)
    (q : (unifSpec + FamilyEncoding.challengeSpec M H R S).Domain)
    (transcript : Transcript M H R S) :
    Prod.map id (decodeTranscript bridge.problem.hash pp) <$>
        ((oracles bridge.problem pp ∘ₛ bridge.liftedOracles pp) q).run transcript =
      (FamilyEncoding.oracles bridge.encodingProblem pp q).run
        (decodeTranscript bridge.problem.hash pp transcript) := by
  cases q with
  | inl random =>
    simp [liftedOracles, QueryImpl.compose, oracles, FamilyEncoding.oracles]
  | inr query =>
    have hreject := bridge.rejected_decodeTranscript pp transcript query.1
    by_cases h : rejected bridge.problem.numRecords transcript query.1 = true
    · simp [liftedOracles, QueryImpl.compose, oracles, challengeOracle,
        FamilyEncoding.oracles, FamilyEncoding.challengeOracle, encodingProblem, hreject, h,
        decodeAnswer]
    · have heligible : rejected bridge.problem.numRecords transcript query.1 = false := by
        simpa using h
      have hsample := bridge.sampleResult_decode pp query
      change Prod.map id (decodeTranscript bridge.problem.hash pp) <$>
        (simulateQ (oracles bridge.problem pp)
          (decodeAnswer bridge.problem.hash pp query <$>
            ((unifSpec + challengeSpec M H R S).query (.inr query) :
              OracleComp (unifSpec + challengeSpec M H R S) (Option R)))).run transcript = _
      simp only [simulateQ_map, simulateQ_spec_query]
      change Prod.map id (decodeTranscript bridge.problem.hash pp) <$>
        (decodeAnswer bridge.problem.hash pp query <$>
          challengeOracle bridge.problem pp query).run transcript =
        (FamilyEncoding.challengeOracle bridge.encodingProblem pp query).run
          (decodeTranscript bridge.problem.hash pp transcript)
      rw [FamilyEncoding.challengeOracle_run_of_eligible bridge.encodingProblem pp query
        (decodeTranscript bridge.problem.hash pp transcript)
        (by simpa [encodingProblem, hreject] using heligible)]
      rw [← hsample]
      simp [challengeOracle, heligible, decodeTranscript, decodeRecord]

/-- The complete adaptive decoded transcript law. This is an equality of computations, hence
retains all returned failures and missing mass, rather than conditioning on successful output. -/
theorem run_decode (bridge : AcceptedBridge PP M H R Y S) (pp : PP) {α : Type}
    (program : OracleComp (unifSpec + FamilyEncoding.challengeSpec M H R S) α)
    (transcript : Transcript M H R S) :
    Prod.map id (decodeTranscript bridge.problem.hash pp) <$>
        (simulateQ (oracles bridge.problem pp)
          (simulateQ (bridge.liftedOracles pp) program)).run transcript =
      (simulateQ (FamilyEncoding.oracles bridge.encodingProblem pp) program).run
        (decodeTranscript bridge.problem.hash pp transcript) := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (oracles bridge.problem pp ∘ₛ bridge.liftedOracles pp)
    (FamilyEncoding.oracles bridge.encodingProblem pp)
    (decodeTranscript bridge.problem.hash pp) (bridge.oracles_decode pp) program transcript

/-- The explicit native hash adversary is the source program under the public decoding adapter. -/
@[expose] def reduction (bridge : AcceptedBridge PP M H R Y S)
    (source : FamilyEncoding.Adversary bridge.encodingProblem) : Adversary bridge.problem where
  find pp := simulateQ (bridge.liftedOracles pp) (source.find pp)

/-- Actual successful source records give both accepted full hashes. Restricted injectivity is
applied only after establishing those two acceptance equations at the same coordinate. -/
theorem valid_implies_hash_collision
    [DecidableEq M] [DecidableEq H] [DecidableEq R] [DecidableEq Y]
    (bridge : AcceptedBridge PP M H R Y S) (pp : PP)
    (transcript : Transcript M H R S) (candidate : FamilyEncoding.Forgery M H R S)
    (hformed : FamilyEncoding.WellFormed bridge.family pp
      (decodeTranscript bridge.problem.hash pp transcript))
    (hwin : FamilyEncoding.valid bridge.family pp
      (decodeTranscript bridge.problem.hash pp transcript) candidate = true) :
    valid bridge.problem.hash pp transcript candidate = true := by
  unfold FamilyEncoding.valid at hwin
  cases hcand : bridge.family.value candidate.query.1 pp candidate.query.2 candidate.randomizer with
  | none => simp [hcand] at hwin
  | some word =>
    simp only [hcand, decodeTranscript, List.any_map, List.any_eq_true] at hwin
    obtain ⟨entry, hmem, hwitness⟩ := hwin
    cases hresult : entry.result with
    | none => simp [decodeRecord, decodeAnswer, hresult] at hwitness
    | some r =>
      have hconditions : entry.position = candidate.query.1 ∧
          bridge.problem.hash.word entry.position
            (bridge.problem.hash.eval pp ⟨entry.position, entry.message⟩ r) = word ∧
          ((⟨entry.position, entry.message⟩ : FamilyEncoding.Query M H S), r) ≠
            (candidate.query, candidate.randomizer) := by
        simpa only [Function.comp_apply, decodeRecord, decodeAnswer, hresult,
          Option.map_some, decide_eq_true_eq] using hwitness
      have hentry : decodeRecord bridge.problem.hash pp entry ∈
          decodeTranscript bridge.problem.hash pp transcript := List.mem_map.mpr ⟨entry, hmem, rfl⟩
      have hvalue := hformed (decodeRecord bridge.problem.hash pp entry) hentry
        (bridge.problem.hash.word entry.position
          (bridge.problem.hash.eval pp ⟨entry.position, entry.message⟩ r)) r
        (by simp [decodeRecord, decodeAnswer, hresult])
      have hold := bridge.accepted_of_value_eq_some pp ⟨entry.position, entry.message⟩ r
        (bridge.problem.hash.word entry.position
          (bridge.problem.hash.eval pp ⟨entry.position, entry.message⟩ r)) hvalue
      have hnew := bridge.accepted_of_value_eq_some pp candidate.query
        candidate.randomizer word hcand
      have hhash : bridge.problem.hash.eval pp ⟨entry.position, entry.message⟩ r =
          bridge.problem.hash.eval pp candidate.query candidate.randomizer := by
        apply bridge.word_injOn entry.position hold.1
        · simpa only [Set.mem_ofPred_eq, hconditions.1] using hnew.1
        · simpa only [hconditions.1] using hconditions.2.1.trans hnew.2
      simp only [valid, hnew.1, Bool.true_and, List.any_eq_true]
      refine ⟨entry, hmem, ?_⟩
      simp [hresult, hconditions.1, hhash, hconditions.2.2]

/-- The common returned sample includes the native history before either Boolean win test. -/
@[expose] def runNative (bridge : AcceptedBridge PP M H R Y S)
    (source : FamilyEncoding.Adversary bridge.encodingProblem) :
    ProbComp (PP × (FamilyEncoding.Forgery M H R S × Transcript M H R S)) := do
  let pp ← bridge.problem.paramGen
  let out ← (simulateQ (oracles bridge.problem pp) ((bridge.reduction source).find pp)).run []
  return (pp, out)

/-- Observe the exact source winning condition on the publicly decoded native history. -/
@[expose] def sourceObservation [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (bridge : AcceptedBridge PP M H R Y S)
    (result : PP × (FamilyEncoding.Forgery M H R S × Transcript M H R S)) : Bool :=
  FamilyEncoding.valid bridge.family result.1
    (decodeTranscript bridge.problem.hash result.1 result.2.2) result.2.1

/-- Observe the native full-hash winning condition on the same returned sample. -/
@[expose] def targetObservation
    [DecidableEq M] [DecidableEq H] [DecidableEq R] [DecidableEq Y]
    (bridge : AcceptedBridge PP M H R Y S)
    (result : PP × (FamilyEncoding.Forgery M H R S × Transcript M H R S)) : Bool :=
  valid bridge.problem.hash result.1 result.2.2 result.2.1

/-- Every native execution decodes to a source execution with all successful record equations. -/
theorem decoded_run_wellFormed (bridge : AcceptedBridge PP M H R Y S) (pp : PP)
    (source : FamilyEncoding.Adversary bridge.encodingProblem)
    (out : FamilyEncoding.Forgery M H R S × Transcript M H R S)
    (hout : out ∈ support
      ((simulateQ (oracles bridge.problem pp) ((bridge.reduction source).find pp)).run [])) :
    FamilyEncoding.WellFormed bridge.family pp
      (decodeTranscript bridge.problem.hash pp out.2) := by
  have hproj := bridge.run_decode pp (source.find pp) []
  simp only [decodeTranscript, List.map_nil] at hproj
  have hsource : (out.1, decodeTranscript bridge.problem.hash pp out.2) ∈
      support ((simulateQ (FamilyEncoding.oracles bridge.encodingProblem pp)
        (source.find pp)).run []) := by
    rw [← hproj]
    rw [support_map]
    exact ⟨out, hout, rfl⟩
  exact FamilyEncoding.run_preserves_wellFormed bridge.encodingProblem pp (source.find pp)
    [] (by simp [FamilyEncoding.WellFormed]) _ hsource

/-- The source experiment is exactly its Boolean observation of the native returned sample. -/
theorem source_experiment_eq_native
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (bridge : AcceptedBridge PP M H R Y S)
    (source : FamilyEncoding.Adversary bridge.encodingProblem) :
    FamilyEncoding.experiment source = bridge.sourceObservation <$> bridge.runNative source := by
  unfold FamilyEncoding.experiment runNative sourceObservation
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply congrArg (fun f => bridge.problem.paramGen >>= f)
  funext pp
  have hproj := bridge.run_decode pp (source.find pp) []
  simp only [decodeTranscript, List.map_nil] at hproj
  rw [← hproj]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, reduction]
  rfl

/-- The native experiment evaluates the native Boolean observation of the same sample. -/
theorem target_experiment_eq_native
    [DecidableEq M] [DecidableEq H] [DecidableEq R] [DecidableEq Y]
    (bridge : AcceptedBridge PP M H R Y S)
    (source : FamilyEncoding.Adversary bridge.encodingProblem) :
    experiment (bridge.reduction source) =
      bridge.targetObservation <$> bridge.runNative source := by
  simp only [experiment, runNative, targetObservation, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind]

/-- Every returned source win in the common native execution is an accepted full-hash collision. -/
theorem sourceObservation_implies_targetObservation
    [DecidableEq M] [DecidableEq H] [DecidableEq R] [DecidableEq Y]
    (bridge : AcceptedBridge PP M H R Y S)
    (source : FamilyEncoding.Adversary bridge.encodingProblem)
    (result : PP × (FamilyEncoding.Forgery M H R S × Transcript M H R S))
    (hresult : result ∈ support (bridge.runNative source))
    (hwin : bridge.sourceObservation result = true) : bridge.targetObservation result = true := by
  unfold runNative at hresult
  obtain ⟨pp, _, hrest⟩ := support_bind_exists hresult
  obtain ⟨out, hout, hpure⟩ := support_bind_exists hrest
  have heq := (mem_support_pure_iff _ _).mp hpure
  subst result
  exact bridge.valid_implies_hash_collision pp out.2 out.1
    (bridge.decoded_run_wellFormed pp source out hout) hwin

/-- The named accepted-output reduction preserves the entire adaptive challenge law and bounds
unconditional source winning mass by the actual strategy-indexed hash advantage. This statement
contains no comparison to an IID retry primitive. -/
theorem advantage_le_hash
    [DecidableEq M] [DecidableEq H] [DecidableEq R] [DecidableEq Y]
    (bridge : AcceptedBridge PP M H R Y S)
    (source : FamilyEncoding.Adversary bridge.encodingProblem) :
    FamilyEncoding.advantage source ≤ advantage (bridge.reduction source) := by
  unfold FamilyEncoding.advantage FamilyEncoding.outputMeasure advantage
  rw [bridge.source_experiment_eq_native source, bridge.target_experiment_eq_native source]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support (bridge.runNative source)
    (fun result => pure (bridge.sourceObservation result))
    (fun result => pure (bridge.targetObservation result)) (measurableSet_singleton true)
  intro result hresult
  by_cases hwin : bridge.sourceObservation result = true
  · have htarget := bridge.sourceObservation_implies_targetObservation source result hresult hwin
    simp [hwin, htarget]
  · have hlose : bridge.sourceObservation result = false := by
      cases h : bridge.sourceObservation result <;> simp_all
    simp [hlose]

end AcceptedBridge

end GXMSS.Hypertree.Security.FamilyEncodingAcceptedOutput
