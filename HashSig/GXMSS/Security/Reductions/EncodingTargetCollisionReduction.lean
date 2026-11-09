/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.EncodingAcceptedOutput

/-!
# Encoding collision transport

A public-seed-compatible encoding bridge transports encoding target collisions to the
underlying message-hash target-collision game.
-/

public section

namespace GXMSS.Encoding.TargetCollisionReduction

open OracleComp OracleSpec TargetCollisionResistance TweakableHash

variable {PP M R E Tweak Y : Type} {n radix : ℕ}

/-- Data needed to compare the full encoding word with one tweakable-hash output. The success law
includes returned failure, so the target-sum instance cannot silently register failed draws. -/
structure Bridge (PP M R E Tweak Y : Type) (n radix : ℕ) where
  /-- Randomized incomparable encoding connected to the message hash. -/
  enc : IncomparableEncoding PP M R E n radix
  /-- Tweakable message hash on message/randomizer pairs. -/
  th : TweakableHash PP Tweak (M × R) Y
  /-- Address of the message-hash computation for each epoch. -/
  epochToTweak : E → Tweak
  epochToTweak_injective : Function.Injective epochToTweak
  /-- Test identifying hash outputs accepted by the encoding. -/
  accepts : Y → Bool
  /-- Codeword associated with each message-hash output. -/
  word : Y → Codeword n radix
  word_injective : Function.Injective word
  value_eq : ∀ pp msg r ep,
    enc.value pp msg r ep =
      if accepts (th.eval pp (epochToTweak ep) (msg, r)) then
        some (word (th.eval pp (epochToTweak ep) (msg, r))) else none

/-- The globally injective bridge supplies the shared transport with its historical word-equality
record predicate. Acceptedness is not inferred from that predicate. -/
@[expose, reducible] def Bridge.toTransport (bridge : Bridge PP M R E Tweak Y n radix) :
    TargetCollisionTransport.Bridge PP M R E Tweak Y n radix where
  enc := bridge.enc
  th := bridge.th
  epochToTweak := bridge.epochToTweak
  epochToTweak_injective := bridge.epochToTweak_injective
  accepts := bridge.accepts
  word := bridge.word
  value_eq := bridge.value_eq
  RecordValid pp entry := ∀ word r, entry.result = some (word, r) →
    word = bridge.word (bridge.th.eval pp (bridge.epochToTweak entry.epoch) (entry.message, r))
  recordValid_of_values pp entry h word r hresult := by
    have hvalue := h word r hresult
    rw [bridge.value_eq] at hvalue
    split_ifs at hvalue
    exact Option.some.inj hvalue.symm
  hash_eq_of_recordValid pp entry h word r hresult msg r' hvalue := by
    apply bridge.word_injective
    have hold := h word r hresult
    rw [bridge.value_eq] at hvalue
    split_ifs at hvalue
    exact hold.symm.trans (Option.some.inj hvalue).symm


/-- Both games use the same public-seed draw, record capacity, and retry capacity. -/
@[expose] def encodingProblem [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) :
    TargetCollisionResistance.Problem PP M R E n radix :=
  TargetCollisionTransport.encodingProblem bridge.toTransport p K

/-- The VCVio target game uses the hash word and the encoding success predicate. -/
@[expose] def hashProblem (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) :
    SM_DT_RTCR_Problem PP Tweak M R Y :=
  TargetCollisionTransport.hashProblem bridge.toTransport p K

/-- VCVio's canonical finite randomizer draw is uniform and lossless in the native runtime. -/
theorem canonicalRandomizer_uniform [Fintype R] [SampleableType R] :
    UniformSampler ProbCompRuntime.probComp ($ᵗ R) := by
  exact TargetCollisionTransport.canonicalRandomizer_uniform

/-- A successful source record contributes its randomizer; exhaustion remains an occupied slot. -/
@[expose] def targetRecord (bridge : Bridge PP M R E Tweak Y n radix)
    (entry : TargetCollisionResistance.Record M R E n radix) : Tweak × M × Option R :=
  TargetCollisionTransport.targetRecord bridge.toTransport entry

/-- The target history retains every eligible source query in its original order. -/
@[expose] def targetHistory (bridge : Bridge PP M R E Tweak Y n radix)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) :
    SM_DT_RTCR_State Tweak M R :=
  TargetCollisionTransport.targetHistory bridge.toTransport transcript

/-- Transcript conversion preserves the cap even when a query exhausted its retries. -/
theorem targetHistory_length (bridge : Bridge PP M R E Tweak Y n radix)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) :
    (targetHistory bridge transcript).length = transcript.length := by
  exact TargetCollisionTransport.targetHistory_length bridge.toTransport transcript

/-- Each accepted target keeps its source index, including failed slots. -/
theorem targetHistory_getElem? (bridge : Bridge PP M R E Tweak Y n radix)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) (index : ℕ) :
    (targetHistory bridge transcript)[index]? =
      (transcript[index]?).map (targetRecord bridge) := by
  exact TargetCollisionTransport.targetHistory_getElem? bridge.toTransport transcript index

/-- Injective epoch mapping makes repeated-epoch rejection agree with reserved tweaks. -/
theorem used_iff_tweakReserved [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) (ep : E) :
    TargetCollisionResistance.used transcript ep = true ↔
      TweakReserved Prod.fst (targetHistory bridge transcript) (bridge.epochToTweak ep) := by
  exact TargetCollisionTransport.used_iff_tweakReserved bridge.toTransport transcript ep

/-- The two challenge handlers reject the same full or reused query. -/
theorem rejected_iff_target_rejected [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p : ℕ)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) (ep : E) :
    TargetCollisionResistance.rejected p transcript ep = true ↔
      p ≤ (targetHistory bridge transcript).length ∨
        TweakReserved Prod.fst (targetHistory bridge transcript) (bridge.epochToTweak ep) := by
  exact TargetCollisionTransport.rejected_iff_target_rejected bridge.toTransport p transcript ep

/-- The source and target retry loops make the same draws. Only the returned hash word is mapped
to the full encoding word; returned exhaustion and missing mass are preserved by `map`. -/
theorem retry_eq_resample [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (pp : PP) (msg : M) (ep : E) :
    bridge.enc.retry ($ᵗ R) pp msg ep K =
      (SM_DT_RTCR_resample (hashProblem bridge p K) pp (bridge.epochToTweak ep) msg K).map
        (Option.map fun pair => (bridge.word pair.1, pair.2)) := by
  exact TargetCollisionTransport.retry_eq_resample bridge.toTransport p K pp msg ep

/-- A returned successful retry has the full word of its underlying hash evaluation. -/
theorem word_eq_of_mem_retry [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (msg : M) (ep : E) (K : ℕ) (word : Codeword n radix) (r : R)
    (hreturned : some (word, r) ∈ support (bridge.enc.retry ($ᵗ R) pp msg ep K)) :
    word = bridge.word (bridge.th.eval pp (bridge.epochToTweak ep) (msg, r)) := by
  exact TargetCollisionTransport.word_eq_of_mem_retry
    bridge.toTransport pp msg ep K word r hreturned

/-- This is the exact source winning predicate for one transcript entry. -/
@[expose] def witnesses (bridge : Bridge PP M R E Tweak Y n radix)
    (pp : PP) (collision : M × R × E)
    [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (entry : TargetCollisionResistance.Record M R E n radix) : Bool :=
  TargetCollisionTransport.witnesses bridge.toTransport pp collision entry

/-- The target index is the first source record that witnesses the submitted collision. If no
record witnesses it, the index is the out-of-range value `transcript.length`. -/
@[expose] def witnessIndex [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (collision : M × R × E) : ℕ :=
  TargetCollisionTransport.witnessIndex bridge.toTransport pp transcript collision

/-- The source win test is precisely the existence of an entry selected by the index search. -/
theorem valid_iff_witness [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (collision : M × R × E) :
    TargetCollisionResistance.valid bridge.enc pp transcript collision = true ↔
      ∃ entry ∈ transcript, witnesses bridge pp collision entry = true := by
  exact TargetCollisionTransport.valid_iff_witness bridge.toTransport pp transcript collision

/-- Every returned successful target word is the bridge's full word for the recorded hash output.
This is an invariant of the challenge simulation, not a property of arbitrary user data. -/
@[expose] def WellFormed (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) : Prop :=
  ∀ entry ∈ transcript, ∀ word r, entry.result = some (word, r) →
    word = bridge.word (bridge.th.eval pp (bridge.epochToTweak entry.epoch)
      (entry.message, r))

/-- A well-formed source collision names a VCVio target at the same issue index. -/
theorem valid_implies_hash_collision [DecidableEq M] [DecidableEq R] [DecidableEq E]
    [DecidableEq Y]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (collision : M × R × E) (hformed : WellFormed bridge pp transcript)
    (hwin : TargetCollisionResistance.valid bridge.enc pp transcript collision = true) :
    SM_DT_RTCR_IsCollision (hashProblem bridge p K) pp (targetHistory bridge transcript)
      (witnessIndex bridge pp transcript collision, collision.1, collision.2.1) = true := by
  exact TargetCollisionTransport.valid_implies_hash_collision
    bridge.toTransport p K pp transcript collision hformed hwin

/-- Each source challenge query is forwarded to the corresponding hash challenge and its returned
word is lifted. Recording through `finish` retains rejected queries and exhausted entries. -/
@[expose] def challengeLift [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p : ℕ) :
    QueryImpl (TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix)
        (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))) :=
  TargetCollisionTransport.challengeLift bridge.toTransport p

/-- Private random queries pass through unchanged; challenge queries use `challengeLift`. -/
@[expose] def liftedOracles [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p : ℕ) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix)
        (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))) :=
  TargetCollisionTransport.liftedOracles bridge.toTransport p

/-- Flattening the nested source and hash challenge handlers exposes both ordered histories. -/
@[expose] noncomputable def coupledOracles [DecidableEq E] [DecidableEq Tweak]
    [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) :=
  TargetCollisionTransport.coupledOracles bridge.toTransport p K pp

/-- A direct coupled source handler mirrors the encoding challenge and records the corresponding
hash target. The second history remains a projection of the first. -/
@[expose] def sourceCoupledChallenge [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) :=
  TargetCollisionTransport.sourceCoupledChallenge bridge.toTransport p K pp

/-- Private random draws have the same meaning in the direct coupled source game. -/
@[expose] def sourceCoupledOracles [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) :=
  TargetCollisionTransport.sourceCoupledOracles bridge.toTransport p K pp

/-- The source record word and hash history agree with the pinned target game. -/
@[expose] def CoupledInv (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) : Prop :=
  state.2 = targetHistory bridge state.1 ∧ WellFormed bridge pp state.1

/-- The two histories start empty and agree. -/
theorem coupledInv_empty (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP) :
    CoupledInv bridge pp ([], []) := by
  exact TargetCollisionTransport.coupledInv_empty bridge.toTransport pp

/-- Under the history relation, one source query and its hash simulation have identical
returned values and next states. -/
theorem coupledOracles_eq_sourceCoupled_of_inv
    [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state) :
    (coupledOracles bridge p K pp q).run state =
      (sourceCoupledOracles bridge p K pp q).run state := by
  exact TargetCollisionTransport.coupledOracles_eq_sourceCoupled_of_inv
    bridge.toTransport p K pp q state hinv

/-- The direct challenge handler maintains history alignment and full-word correctness on every
returned path. Missing execution mass contributes no path and is left unchanged. -/
theorem sourceCoupledChallenge_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : M × E)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : Option (Codeword n radix × R) ×
      (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((sourceCoupledChallenge bridge p K pp q).run state)) :
    CoupledInv bridge pp out.2 := by
  exact TargetCollisionTransport.sourceCoupledChallenge_preserves_inv
    bridge.toTransport p K pp q state hinv out hout

/-- Ordinary random draws leave both histories alone; the challenge case uses the preceding
invariant lemma. -/
theorem sourceCoupledOracles_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Range q ×
      (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((sourceCoupledOracles bridge p K pp q).run state)) :
    CoupledInv bridge pp out.2 := by
  exact TargetCollisionTransport.sourceCoupledOracles_preserves_inv
    bridge.toTransport p K pp q state hinv out hout

/-- Adaptive source and target simulations agree on the full paired state from an aligned
starting point. The theorem is an equality of partial computations, so returned failure and
unreturned mass are retained. -/
theorem coupled_run_eq_source [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state) :
    (simulateQ (coupledOracles bridge p K pp) program).run state =
      (simulateQ (sourceCoupledOracles bridge p K pp) program).run state := by
  exact TargetCollisionTransport.coupled_run_eq_source bridge.toTransport p K pp program state hinv

/-- Forgetting the target history gives exactly the source challenge handler. -/
theorem sourceCoupledOracles_proj [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) :
    Prod.map id Prod.fst <$> (sourceCoupledOracles bridge p K pp q).run state =
      (TargetCollisionResistance.oracles (encodingProblem bridge p K) pp q).run state.1 := by
  exact TargetCollisionTransport.sourceCoupledOracles_proj bridge.toTransport p K pp q state

/-- Source simulation is the first projection of the direct paired simulation. -/
theorem sourceCoupled_run_proj [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) :
    Prod.map id Prod.fst <$> (simulateQ (sourceCoupledOracles bridge p K pp) program).run state =
      (simulateQ (TargetCollisionResistance.oracles (encodingProblem bridge p K) pp)
        program).run state.1 := by
  exact TargetCollisionTransport.sourceCoupled_run_proj bridge.toTransport p K pp program state

/-- Every returned path of an adaptive source adversary retains the coupled history invariant. -/
theorem sourceCoupled_run_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : α × (TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((simulateQ (sourceCoupledOracles bridge p K pp) program).run state)) :
    CoupledInv bridge pp out.2 := by
  exact TargetCollisionTransport.sourceCoupled_run_preserves_inv
    bridge.toTransport p K pp program state hinv out hout

/-- Flattening the hash game around the source adversary yields the same coupled program from
empty histories. This equality includes both histories and every returned failure. -/
theorem nested_run_eq_source [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α) :
    (simulateQ (SM_DT_RTCR_oracles (hashProblem bridge p K) pp)
      ((simulateQ (liftedOracles bridge p) program).run [])).run
        ([] : SM_DT_RTCR_State Tweak M R) =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceCoupledOracles bridge p K pp) program).run ([], []) := by
  exact TargetCollisionTransport.nested_run_eq_source bridge.toTransport p K pp program

/-- The hash adversary runs the source adversary under the translated challenge oracle, then
reports the first successful source target's index and the same candidate pair. -/
@[expose] def reduction [SampleableType R] [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    SM_DT_RTCR_Adversary (hashProblem bridge p K) :=
  TargetCollisionTransport.reduction bridge.toTransport p K source

/-- The common returned sample keeps both ordered histories without conditioning on termination. -/
@[expose] def runCoupled [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    ProbComp (PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) :=
  TargetCollisionTransport.runCoupled bridge.toTransport p K source

/-- Boolean source observation on the common returned sample. -/
@[expose] def sourceObservation [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix)
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) : Bool :=
  TargetCollisionTransport.sourceObservation bridge.toTransport result

/-- Boolean VCVio observation on the same sample and first witnessing index. -/
@[expose] def targetObservation [DecidableEq M] [DecidableEq R] [DecidableEq E]
    [DecidableEq Y]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) : Bool :=
  TargetCollisionTransport.targetObservation bridge.toTransport p K result

/-- Every returned source win is a target win at the selected issue index. False results and
missing mass are unrestricted, which is sufficient for the native measure inequality. -/
theorem sourceObservation_implies_targetObservation
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Y]
    [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K))
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R)))
    (hresult : result ∈ support (runCoupled bridge p K source))
    (hwin : sourceObservation bridge result = true) :
    targetObservation bridge p K result = true := by
  exact TargetCollisionTransport.sourceObservation_implies_targetObservation
    bridge.toTransport p K source result hresult hwin

/-- The source Boolean experiment is the first-history observation of the common sample. -/
theorem source_experiment_eq_coupled
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    TargetCollisionResistance.experiment source =
      sourceObservation bridge <$> runCoupled bridge p K source := by
  exact TargetCollisionTransport.source_experiment_eq_coupled bridge.toTransport p K source

/-- The VCVio experiment of the constructed adversary observes the same common sample. -/
theorem target_experiment_eq_coupled
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq Y] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    SM_DT_RTCR_Experiment (reduction bridge p K source) =
      targetObservation bridge p K <$> runCoupled bridge p K source := by
  exact TargetCollisionTransport.target_experiment_eq_coupled bridge.toTransport p K source

/-- The unconditional native returned-mass bound for any capacities, including zero. Both games
sample the same public seed and use the canonical randomizer sampler; no mass is normalized. -/
theorem advantage_le_hash
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq Y] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    TargetCollisionResistance.advantage source ≤
      SM_DT_RTCR_Advantage (reduction bridge p K source) := by
  exact TargetCollisionTransport.advantage_le_hash bridge.toTransport p K source

end GXMSS.Encoding.TargetCollisionReduction
