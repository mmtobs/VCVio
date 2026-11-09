/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses

/-!
# Global mixed-family encoding collision reduction

The reduction registers every upper certificate once, retains optional results including
exhaustion, and answers first global signing requests through the bottom encoding challenge.
Its transcript uses complete one-time-key coordinates and exact message/randomizer-pair freshness.
-/

public section

namespace GXMSS.Hypertree.Security

open Encoding OracleComp OracleSpec
open scoped ENNReal

variable {PP T X H M R Coins : Type} {S : Shape}

/-- The one family game has room for all eager upper records and the permitted signing calls. -/
@[expose] def familyEncodingProblem (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (qs : ℕ) :
    FamilyEncoding.Problem PP M H R S where
  family := family
  sampling := sampling
  paramGen := hash.thf.seedGen
  numRecords := qs + upperCount S

/-- The bottom encoding candidate extracted from a complete forgery. -/
@[expose] def bottomEncodingCandidate
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S)) :
    FamilyEncoding.Forgery M H R S :=
  ⟨⟨bottomPosition S forgery.1, bottomMessage forgery.1 forgery.2.1⟩,
    forgery.2.2.bottom.randomizer⟩

/-- An internal encoding candidate uses the actually recovered child root as its message. -/
@[expose] def upperEncodingCandidate (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S))
    (i : Fin (S.d - 1)) : Option (FamilyEncoding.Forgery M H R S) := do
  let child ← recoverThrough hash family pp forgery.1 forgery.2.1 forgery.2.2 i.val
    (by have := i.isLt; omega)
  pure ⟨⟨(upperPositionAt S forgery.1 i).1,
    internalMessage (upperPositionAt S forgery.1 i) child⟩, (forgery.2.2.upper i).randomizer⟩

/-- All concrete message/randomizer candidates exposed by a forgery, bottom to top. -/
@[expose] def encodingCandidates (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S)) :
    List (FamilyEncoding.Forgery M H R S) :=
  bottomEncodingCandidate forgery ::
    (List.ofFn (upperEncodingCandidate hash family pp forgery)).filterMap id

/-- Select the first actual family collision, with a fixed bottom candidate if none exists. -/
@[expose] def selectEncodingCandidate [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ledger : FamilyEncoding.Transcript M H R S)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S)) :
    FamilyEncoding.Forgery M H R S :=
  ((encodingCandidates hash family pp forgery).find? (FamilyEncoding.valid family pp ledger)).getD
    (bottomEncodingCandidate forgery)

/-- A component candidate observed only as its exact encoding-game query and randomizer. -/
@[expose] def candidateEncoding (candidate : Unforgeability.ComponentCandidate M R H S) :
    FamilyEncoding.Forgery M H R S :=
  ⟨⟨candidate.position, candidate.message⟩, candidate.signature.randomizer⟩

/-- Every concrete component read by verification occurs in the reduction's candidate scan. -/
theorem candidateAt_mem_encodingCandidates (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S))
    (layer : ℕ) (hlayer : layer < S.d) (candidate : Unforgeability.ComponentCandidate M R H S)
    (h : Unforgeability.candidateAt? hash family pp forgery.1 forgery.2.1 forgery.2.2
      layer hlayer = some candidate) :
    candidateEncoding candidate ∈ encodingCandidates hash family pp forgery := by
  cases layer with
  | zero =>
    cases Option.some.inj h
    simp [candidateEncoding, encodingCandidates, bottomEncodingCandidate]
  | succ layer =>
    let i : Fin (S.d - 1) := ⟨layer, by omega⟩
    have hupper : upperEncodingCandidate hash family pp forgery i =
        some (candidateEncoding candidate) := by
      cases hchild : recoverThrough hash family pp forgery.1 forgery.2.1 forgery.2.2
          layer (by omega) with
      | none => simp [Unforgeability.candidateAt?, hchild] at h
      | some child =>
        have heq : candidate =
            ⟨(upperPositionAt S forgery.1 i).1,
              internalMessage (upperPositionAt S forgery.1 i) child,
              forgery.2.2.upper i⟩ := by
          simpa [Unforgeability.candidateAt?, hchild, i] using h.symm
        subst candidate
        simp [upperEncodingCandidate, candidateEncoding, hchild, i]
    apply List.mem_cons_of_mem
    exact List.mem_filterMap.mpr
      ⟨some (candidateEncoding candidate), List.mem_ofFn.mpr ⟨i, hupper⟩, rfl⟩

/-- If any concrete scan candidate wins, the actual selected candidate wins. -/
theorem selectEncodingCandidate_valid_of_mem [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ledger : FamilyEncoding.Transcript M H R S)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S))
    (candidate : FamilyEncoding.Forgery M H R S)
    (hmem : candidate ∈ encodingCandidates hash family pp forgery)
    (hvalid : FamilyEncoding.valid family pp ledger candidate = true) :
    FamilyEncoding.valid family pp ledger
      (selectEncodingCandidate hash family pp ledger forgery) = true := by
  cases hfind : (encodingCandidates hash family pp forgery).find?
      (FamilyEncoding.valid family pp ledger) with
  | none =>
    have hfalse := (List.find?_eq_none.mp hfind) candidate hmem
    exact (hfalse hvalid).elim
  | some selected =>
    have hselected := List.find?_some hfind
    simpa only [selectEncodingCandidate, hfind, Option.getD_some] using hselected

/-- The encoding-collision event observes the complete actual source ledger. -/
@[expose] noncomputable def encodingCollisionObservation
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Result PP H M R Coins S) : Bool :=
  FamilyEncoding.valid family out.pk.seed (encodingLedger hash out)
    (selectEncodingCandidate hash family out.pk.seed (encodingLedger hash out) out.forgery)

/-- Ask the actual mixed-family encoding oracle at one complete coordinate. -/
@[expose] def encodingQuery (q : FamilyEncoding.Query M H S) :
    OracleComp (unifSpec + FamilyEncoding.challengeSpec M H R S)
      (Option (Codeword S.v (2 ^ S.w) × R)) :=
  liftM ((unifSpec + FamilyEncoding.challengeSpec M H R S).query (.inr q))

/-- One primitive family query is interpreted by the actual challenge handler. -/
theorem run_encodingQuery (prob : FamilyEncoding.Problem PP M H R S) (pp : PP)
    (q : FamilyEncoding.Query M H S) (ledger : FamilyEncoding.Transcript M H R S) :
    (simulateQ (FamilyEncoding.oracles prob pp) (encodingQuery q)).run ledger =
      (FamilyEncoding.challengeOracle prob pp q).run ledger := by
  simp only [encodingQuery, simulateQ_spec_query, FamilyEncoding.oracles,
    QueryImpl.add_apply_inr]

/-- A finite sequence of fresh distinct coordinate queries samples exactly their configured
results and appends every occupied slot in order. The cap includes failed attempts. -/
theorem run_encodingQuery_mOfFn (prob : FamilyEncoding.Problem PP M H R S) (pp : PP)
    (k : ℕ) (queries : Fin k → FamilyEncoding.Query M H S)
    (ledger : FamilyEncoding.Transcript M H R S)
    (hinj : Function.Injective (fun i => (queries i).1))
    (hfresh : ∀ i, FamilyEncoding.used ledger (queries i).1 = false)
    (hspace : ledger.length + k ≤ prob.numRecords) :
    (simulateQ (FamilyEncoding.oracles prob pp)
      (Fin.mOfFn k fun i => encodingQuery (queries i))).run ledger =
      (fun answers => (answers, ledger ++ List.ofFn (fun i =>
        (⟨(queries i).1, (queries i).2, answers i⟩ : FamilyEncoding.Record M H R S)))) <$>
        Fin.mOfFn k (fun i => FamilyEncoding.sampleResult prob pp (queries i)) := by
  induction k generalizing ledger with
  | zero => simp [Fin.mOfFn]
  | succ k ih =>
    have heligible : FamilyEncoding.rejected prob.numRecords ledger (queries 0).1 = false := by
      have hlen : ledger.length < prob.numRecords := by omega
      simp [FamilyEncoding.rejected, hfresh 0, Nat.not_le_of_gt hlen]
    rw [Fin.mOfFn, simulateQ_bind, StateT.run_bind, run_encodingQuery,
      FamilyEncoding.challengeOracle_run_of_eligible prob pp (queries 0) ledger heligible]
    simp only [Fin.mOfFn, bind_map_left, map_bind, map_pure]
    apply bind_congr
    intro first
    simp only [simulateQ_bind, StateT.run_bind]
    have hinj' : Function.Injective (fun i : Fin k => (queries i.succ).1) :=
      hinj.comp (Fin.succ_injective k)
    have hfresh' : ∀ i : Fin k,
        FamilyEncoding.used (ledger ++ [⟨(queries 0).1, (queries 0).2, first⟩])
          (queries i.succ).1 = false := by
      intro i
      have hne : (queries 0).1 ≠ (queries i.succ).1 := by
        intro heq
        have hbad := hinj heq
        have := congrArg Fin.val hbad
        simp at this
      simpa [FamilyEncoding.used, hne] using hfresh i.succ
    have hspace' : (ledger ++
        [(⟨(queries 0).1, (queries 0).2, first⟩ : FamilyEncoding.Record M H R S)]).length + k ≤
        prob.numRecords := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih (fun i => queries i.succ) _ hinj' hfresh' hspace']
    simp only [simulateQ_pure, StateT.run_pure]
    simp [map_eq_bind_pure_comp, bind_assoc, List.ofFn_succ, List.append_assoc]

/-- Register every fixed upper certificate once through the actual encoding challenge. -/
noncomputable def registerUpper (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S) :
    OracleComp (unifSpec + FamilyEncoding.challengeSpec M H R S)
      (UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) := by
  letI : Fintype (UpperPosition S) := Fintype.ofFinite _
  exact Fintype.mPi fun p => encodingQuery
    ⟨p.1, internalMessage p (componentRoot hash sk.seed sk.endpoints (childTree S p))⟩

/-- Eager upper registration uses every internal coordinate once and retains every returned
failure. Its law is the actual finite independent product of the configured family queries. -/
theorem run_registerUpper (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S) (prob : FamilyEncoding.Problem PP M H R S) (pp : PP)
    (hcap : upperCount S ≤ prob.numRecords) :
    (simulateQ (FamilyEncoding.oracles prob pp) (registerUpper (M := M) hash sk)).run [] =
      (fun results => (results, upperLedgerFromResults (M := M) hash sk results)) <$>
        (by
          letI : Fintype (UpperPosition S) := Fintype.ofFinite _
          exact Fintype.mPi fun p : UpperPosition S => FamilyEncoding.sampleResult prob pp
            ⟨p.1, internalMessage p
              (componentRoot hash sk.seed sk.endpoints (childTree S p))⟩) := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  let e := (Fintype.equivFin (UpperPosition S)).symm
  let queries := fun i : Fin (Fintype.card (UpperPosition S)) =>
    (⟨(e i).1, internalMessage (e i)
      (componentRoot hash sk.seed sk.endpoints (childTree S (e i)))⟩ : FamilyEncoding.Query M H S)
  have hinj : Function.Injective (fun i => (queries i).1) := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hfresh : ∀ i, FamilyEncoding.used ([] : FamilyEncoding.Transcript M H R S)
      (queries i).1 = false := by simp [FamilyEncoding.used]
  have hspace : ([] : FamilyEncoding.Transcript M H R S).length +
      Fintype.card (UpperPosition S) ≤ prob.numRecords := by
    have hc : Fintype.card (UpperPosition S) = upperCount S :=
      (Nat.card_eq_fintype_card).symm.trans (card_upperPosition S)
    simpa [hc] using hcap
  have hrun := run_encodingQuery_mOfFn prob pp _ queries [] hinj hfresh hspace
  unfold registerUpper Fintype.mPi
  simp only [simulateQ_map, StateT.run_map]
  rw [hrun]
  simp only [Functor.map_map, List.nil_append]
  congr 1
  funext answers
  apply Prod.ext
  · rfl
  · simp [upperLedgerFromResults, upperOrder, queries, e, List.map_ofFn,
      Function.comp_def, Equiv.arrowCongr]

/-- Each upper challenge has exactly the optional observation of its own fixed-coin result. -/
theorem sampleResult_upper (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (qs : ℕ) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (p : UpperPosition S) :
    FamilyEncoding.sampleResult (familyEncodingProblem hash family sampling qs) pp
        ⟨p.1, internalMessage p
          (componentRoot hash pp (endpoints hash pp starts) (childTree S p))⟩ =
      (fun coin => (upperResultAt hash family sampling.internal pp starts p coin).output) <$>
        sampling.sampleInternal := by
  simp [FamilyEncoding.sampleResult, familyEncodingProblem, p.property, upperResultAt,
    componentResult_eq_run, keys]

/-- Actual eager upper registration is the optional projection of the key-generation full-result
sampler. No failed certificate is discarded and no raw-tape equality is required. -/
theorem run_registerUpper_fromResults (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (qs : ℕ) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) :
    (simulateQ (FamilyEncoding.oracles (familyEncodingProblem hash family sampling qs) pp)
      (registerUpper (M := M) hash (keys hash pp starts (fun _ => ())).2)).run [] =
      (fun results : UpperResults R S =>
        ((fun p => (results p).output), upperLedgerFromResults (M := M) hash
          (keys hash pp starts (fun _ => ())).2 (fun p => (results p).output))) <$>
        sampleUpperResults hash family sampling.internal pp starts sampling.sampleInternal := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  rw [run_registerUpper hash _ _ pp (by simp [familyEncodingProblem])]
  have hsamples :
      Fintype.mPi (fun p : UpperPosition S =>
        FamilyEncoding.sampleResult (familyEncodingProblem hash family sampling qs) pp
          ⟨p.1, internalMessage p
            (componentRoot hash pp (endpoints hash pp starts) (childTree S p))⟩) =
      (fun results : UpperResults R S => fun p => (results p).output) <$>
        sampleUpperResults hash family sampling.internal pp starts sampling.sampleInternal := by
    rw [map_output_sampleUpperResults]
    congr 1
    funext p
    exact sampleResult_upper hash family sampling qs pp starts p
  change (fun results => (results, upperLedgerFromResults (M := M) hash
      (keys hash pp starts (fun _ => ())).2 results)) <$> _ = _
  simp only [keys]
  rw [hsamples]
  simp only [Functor.map_map]

/-- Reduction-private synchronized history and its complete observed encoding records. -/
abbrev EncodingReductionState (M H R : Type) (S : Shape) :=
  SyncSignatureUnforgeability.History (Epoch S) M (Signature R H S) ×
    FamilyEncoding.Transcript M H R S

/-- Shared first-request handler from an encoding-result responder. Successful bottom results
remain occupied records even if an upper certificate prevents a full signature. -/
@[expose] def encodingSigningOracleWith {m : Type → Type*} [Monad m]
    (respond : FamilyEncoding.Query M H S → m (Option (Codeword S.v (2 ^ S.w) × R)))
    (hash : HashInstance PP T X H S) (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch S) M (Signature R H S))
      (StateT (EncodingReductionState M H R S) m) := fun q state =>
  match state.1 q.1 with
  | some _ => pure (none, state)
  | none => do
      let answer ← respond ⟨bottomPosition S q.1, bottomMessage q.1 q.2⟩
      let signature := signFromResults hash sk upper q.1 answer
      pure (signature, Function.update state.1 q.1 (some (q.2, signature)),
        state.2 ++ [⟨bottomPosition S q.1, bottomMessage q.1 q.2, answer⟩])

/-- The named reduction's signing handler uses the actual mixed encoding oracle. -/
@[expose] def encodingSigningOracle (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch S) M (Signature R H S))
      (StateT (EncodingReductionState M H R S)
        (OracleComp (unifSpec + FamilyEncoding.challengeSpec M H R S))) :=
  encodingSigningOracleWith encodingQuery hash sk upper

/-- The direct local sampler interpretation of the same signing-result handler. -/
@[expose] def sourceEncodingSigningOracles
    (prob : FamilyEncoding.Problem PP M H R S) (pp : PP) (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M (Signature R H S))
      (StateT (EncodingReductionState M H R S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (EncodingReductionState M H R S) ProbComp) +
      encodingSigningOracleWith (FamilyEncoding.sampleResult prob pp) hash sk upper

/-- Ambient private draws and bottom signing challenges of the named reduction. -/
@[expose] def encodingSigningOracles (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M (Signature R H S))
      (StateT (EncodingReductionState M H R S)
        (OracleComp (unifSpec + FamilyEncoding.challengeSpec M H R S))) :=
  (QueryImpl.ofLift unifSpec
    (OracleComp (unifSpec + FamilyEncoding.challengeSpec M H R S))).liftTarget
      (StateT (EncodingReductionState M H R S)
        (OracleComp (unifSpec + FamilyEncoding.challengeSpec M H R S))) +
    encodingSigningOracle (M := M) hash sk upper

/-- First-request consumption agrees with bottom-coordinate reservation in the full ledger. -/
@[expose] def EncodingHistoryMatches (state : EncodingReductionState M H R S) : Prop :=
  ∀ ep, state.1 ep = none ↔ FamilyEncoding.used state.2 (bottomPosition S ep) = false

/-- Eager upper reservations consume no bottom coordinate. -/
theorem used_upperLedger_bottom (hash : HashInstance PP T X H S) (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) (ep : Epoch S) :
    FamilyEncoding.used (upperLedgerFromResults (M := M) hash sk upper) (bottomPosition S ep) =
      false := by
  simp only [FamilyEncoding.used, upperLedgerFromResults, List.any_map, List.any_eq_false]
  intro p _
  simp only [Function.comp_apply, decide_eq_true_eq]
  intro heq
  have h := congrArg (fun p : OTSPosition S => p.1.1.val) heq
  exact p.property (by simpa only [bottomPosition, positionAt_layer, Fin.val_zero] using h)

/-- Empty synchronized history aligns with the complete eager upper ledger. -/
theorem encodingHistoryMatches_initial (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) :
    EncodingHistoryMatches
      (SyncSignatureUnforgeability.emptyHistory,
        upperLedgerFromResults (M := M) hash sk upper) := by
  intro ep
  simp [SyncSignatureUnforgeability.emptyHistory, used_upperLedger_bottom]

/-- Direct encoding-result signing preserves reservation alignment and consumes at most one
record per signing query, including full-signature failure after a successful bottom result. -/
theorem sourceEncodingSigningOracles_step
    (prob : FamilyEncoding.Problem PP M H R S) (pp : PP) (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R))
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)).Domain) (state : EncodingReductionState M H R S)
    (hinv : EncodingHistoryMatches state)
    (out : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)).Range q × EncodingReductionState M H R S)
    (hout : out ∈ support ((sourceEncodingSigningOracles prob pp hash sk upper q).run state)) :
    EncodingHistoryMatches out.2 ∧
      out.2.2.length ≤ state.2.length + (if q.isRight = true then 1 else 0) := by
  cases q with
  | inl uniform =>
    change out ∈ support
      ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at hout
    obtain ⟨answer, _, hret⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq := (mem_support_pure_iff _ _).mp hret
    subst out
    exact ⟨hinv, by simp⟩
  | inr q =>
    rcases q with ⟨ep, msg⟩
    change out ∈ support
      (encodingSigningOracleWith (FamilyEncoding.sampleResult prob pp) hash sk upper
        (ep, msg) state) at hout
    cases hused : state.1 ep with
    | some first =>
      simp only [encodingSigningOracleWith, hused, support_pure, Set.mem_singleton_iff] at hout
      subst out
      exact ⟨hinv, by simp⟩
    | none =>
      simp only [encodingSigningOracleWith, hused, mem_support_bind_iff] at hout
      obtain ⟨answer, _, hret⟩ := hout
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst out
      refine ⟨?_, by simp⟩
      intro ep'
      by_cases heq : ep' = ep
      · subst ep'
        simp [Function.update, FamilyEncoding.used]
      · have hposne : bottomPosition S ep ≠ bottomPosition S ep' := by
          intro hpos
          exact heq ((positionAt_bottom_injective S hpos).symm)
        simpa [Function.update, heq, FamilyEncoding.used, hposne] using hinv ep'

/-- The actual outer family game interpreting the named reduction's signing queries. -/
@[expose] def coupledEncodingOracles
    (prob : FamilyEncoding.Problem PP M H R S) (pp : PP) (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M (Signature R H S))
      (StateT (EncodingReductionState M H R S × FamilyEncoding.Transcript M H R S) ProbComp) :=
  ((FamilyEncoding.oracles prob pp).mapStateTBase
    (encodingSigningOracles hash sk upper)).flattenStateT

/-- One permitted query has the exact direct-sampling law and identical internal/outer ledgers. -/
theorem coupledEncodingOracles_step
    (prob : FamilyEncoding.Problem PP M H R S) (pp : PP) (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R))
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)).Domain) (state : EncodingReductionState M H R S)
    (hmatch : EncodingHistoryMatches state)
    (hspace : q.isRight = true → state.2.length < prob.numRecords) :
    (coupledEncodingOracles prob pp hash sk upper q).run (state, state.2) =
      (fun output => (output.1, output.2, output.2.2)) <$>
        (sourceEncodingSigningOracles prob pp hash sk upper q).run state := by
  rw [coupledEncodingOracles, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  cases q with
  | inl uniform =>
    simp [encodingSigningOracles, sourceEncodingSigningOracles, FamilyEncoding.oracles,
      QueryImpl.ofLift_eq_id', QueryImpl.simulateQ_add_liftM_query_left,
      map_eq_bind_pure_comp, bind_assoc]
  | inr q =>
    rcases q with ⟨ep, msg⟩
    change (fun y => (y.1.1, y.1.2, y.2)) <$>
        (simulateQ (FamilyEncoding.oracles prob pp)
          (encodingSigningOracleWith encodingQuery hash sk upper (ep, msg) state)).run state.2 =
      (fun output => (output.1, output.2, output.2.2)) <$>
        encodingSigningOracleWith (FamilyEncoding.sampleResult prob pp) hash sk upper
          (ep, msg) state
    cases hused : state.1 ep with
    | some first =>
      simp [encodingSigningOracleWith, hused]
    | none =>
      have hfresh : FamilyEncoding.used state.2 (bottomPosition S ep) = false :=
        (hmatch ep).mp hused
      have heligible : FamilyEncoding.rejected prob.numRecords state.2
          (bottomPosition S ep) = false := by
        simp [FamilyEncoding.rejected, hfresh, Nat.not_le_of_gt (hspace (by rfl))]
      simp only [encodingSigningOracleWith, hused, simulateQ_bind, StateT.run_bind]
      rw [run_encodingQuery, FamilyEncoding.challengeOracle_run_of_eligible
        prob pp _ _ heligible]
      simp [map_eq_bind_pure_comp, bind_assoc]

/-- A pathwise signing-query bound gives exact adaptive correspondence with the family game.
The retained upper prefix occupies capacity before any bottom signing request is made. -/
theorem coupledEncoding_run_eq_source {α : Type}
    (prob : FamilyEncoding.Problem PP M H R S) (pp : PP) (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R))
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)) α) (budget : ℕ)
    (hbound : program.IsQueryBoundP (fun q => q.isRight = true) budget)
    (state : EncodingReductionState M H R S) (hmatch : EncodingHistoryMatches state)
    (hspace : state.2.length + budget ≤ prob.numRecords) :
    (simulateQ (coupledEncodingOracles prob pp hash sk upper) program).run (state, state.2) =
      (fun output => (output.1, output.2, output.2.2)) <$>
        (simulateQ (sourceEncodingSigningOracles prob pp hash sk upper) program).run state := by
  induction program using OracleComp.inductionOn generalizing budget state with
  | pure value => simp
  | query_bind q next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind]
    have hroom : q.isRight = true → state.2.length < prob.numRecords := by
      intro hsign
      have hpositive : 0 < budget := hbound.1.resolve_left (by simpa using hsign)
      omega
    rw [coupledEncodingOracles_step prob pp hash sk upper q state hmatch hroom, bind_map_left,
      map_bind]
    apply bind_congr_of_forall_mem_support
    intro output houtput
    obtain ⟨hmatch', hlength⟩ :=
      sourceEncodingSigningOracles_step prob pp hash sk upper q state hmatch output houtput
    have hspace' : output.2.2.length +
        (if q.isRight = true then budget - 1 else budget) ≤ prob.numRecords := by
      cases q with
      | inl uniform =>
        simp only [Sum.isRight, Bool.false_eq_true, ite_false] at hlength ⊢
        omega
      | inr signing =>
        have hpositive : 0 < budget := hbound.1.resolve_left (by simp)
        simp only [Sum.isRight, ite_true] at hlength ⊢
        omega
    rw [ih output.1 (if q.isRight = true then budget - 1 else budget)
      (hbound.2 output.1) output.2 hmatch' hspace']

/-- The nested actual family interpretation of source signing is the direct sampler kernel,
with both complete ledgers retained and equal on every returned path. -/
theorem nestedEncoding_run_eq_source {α : Type}
    (prob : FamilyEncoding.Problem PP M H R S) (pp : PP) (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R))
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)) α) (budget : ℕ)
    (hbound : program.IsQueryBoundP (fun q => q.isRight = true) budget)
    (state : EncodingReductionState M H R S) (hmatch : EncodingHistoryMatches state)
    (hspace : state.2.length + budget ≤ prob.numRecords) :
    (simulateQ (FamilyEncoding.oracles prob pp)
      ((simulateQ (encodingSigningOracles hash sk upper) program).run state)).run state.2 =
      (fun output => ((output.1, output.2), output.2.2)) <$>
        (simulateQ (sourceEncodingSigningOracles prob pp hash sk upper) program).run state := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun output => ((output.1, output.2.1), output.2.2)) <$>
      (simulateQ (coupledEncodingOracles prob pp hash sk upper) program).run (state, state.2) = _
  rw [coupledEncoding_run_eq_source prob pp hash sk upper program budget hbound state hmatch hspace]
  simp only [Functor.map_map]

/-- Ambient start sampling passes unchanged through the actual family game. -/
theorem familyOuter_liftStarts [SampleableType H]
    (prob : FamilyEncoding.Problem PP M H R S) (pp : PP) :
    (simulateQ (FamilyEncoding.oracles prob pp)
      (OracleComp.liftComp (sampleStarts (H := H) S)
        (unifSpec + FamilyEncoding.challengeSpec M H R S))).run [] =
      (fun starts => (starts, ([] : FamilyEncoding.Transcript M H R S))) <$>
        sampleStarts (H := H) S := by
  simp [FamilyEncoding.oracles, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

/-- Erasing full bottom metadata and raw upper coins gives the direct encoding-result handler.
The eager upper prefix is retained as private records and never merged with disclosed history. -/
theorem nativeOracles_encoding_projection
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (sk : SecretKey PP H sampling.internal.Coins S)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)).Domain) (state : NativeState M H R S) :
    Prod.map id (fun st : NativeState M H R S =>
        (st.1, upperLedger hash family sampling.internal sk ++ bottomLedger st.2)) <$>
        (nativeOracles hash family sampling sk q).run state =
      (sourceEncodingSigningOracles (familyEncodingProblem hash family sampling qs) sk.seed hash
        (eraseUpperCoins sk)
        (fun p => (upperResults hash family sampling.internal sk p).output) q).run
          (state.1, upperLedger hash family sampling.internal sk ++ bottomLedger state.2) := by
  cases q with
  | inl uniform =>
    simp [nativeOracles, sourceEncodingSigningOracles, QueryImpl.ofLift_eq_id',
      map_eq_bind_pure_comp, bind_assoc]
  | inr q =>
    rcases q with ⟨ep, msg⟩
    change Prod.map id (fun st : NativeState M H R S =>
        (st.1, upperLedger hash family sampling.internal sk ++ bottomLedger st.2)) <$>
        nativeSigningOracle hash family sampling sk (ep, msg) state =
      encodingSigningOracleWith
        (FamilyEncoding.sampleResult (familyEncodingProblem hash family sampling qs) sk.seed)
        hash (eraseUpperCoins sk)
        (fun p => (upperResults hash family sampling.internal sk p).output) (ep, msg)
        (state.1, upperLedger hash family sampling.internal sk ++ bottomLedger state.2)
    cases hused : state.1 ep with
    | some first =>
      simp [nativeSigningOracle, signingOracleWithAttempts, encodingSigningOracleWith, hused]
    | none =>
      simp only [nativeSigningOracle, signingOracleWithAttempts, encodingSigningOracleWith, hused]
      have hbottom : (bottomPosition S ep).1.1.val = 0 := rfl
      simp only [FamilyEncoding.sampleResult, familyEncodingProblem, hbottom, ↓reduceIte]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      apply bind_congr
      intro coins
      rw [signWithCoins_eq_signFromResults]
      simp [bottomLedger, componentResult_eq_run, List.map_append, List.append_assoc]

/-- The complete adaptive native interaction factors through the exact optional encoding ledger. -/
theorem native_run_encoding_projection
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (sk : SecretKey PP H sampling.internal.Coins S)
    {α : Type}
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)) α) (state : NativeState M H R S) :
    Prod.map id (fun st : NativeState M H R S =>
        (st.1, upperLedger hash family sampling.internal sk ++ bottomLedger st.2)) <$>
        (simulateQ (nativeOracles hash family sampling sk) program).run state =
      (simulateQ (sourceEncodingSigningOracles (familyEncodingProblem hash family sampling qs)
        sk.seed hash (eraseUpperCoins sk)
        (fun p => (upperResults hash family sampling.internal sk p).output)) program).run
          (state.1, upperLedger hash family sampling.internal sk ++ bottomLedger state.2) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _
    (nativeOracles_encoding_projection hash family sampling qs sk) program state

/-- Direct sampled encoding-result simulation at fixed coin-free key material and upper replies. -/
noncomputable def encodingReplayWithKeys [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) : ProbComp Bool := do
  let ledger := upperLedgerFromResults (M := M) hash sk upper
  let (forgery, state) ←
    (simulateQ (sourceEncodingSigningOracles (familyEncodingProblem hash family sampling qs)
      sk.seed hash sk upper) (adv.forge pk)).run
        (SyncSignatureUnforgeability.emptyHistory, ledger)
  pure (FamilyEncoding.valid family pk.seed state.2
    (selectEncodingCandidate hash family pk.seed state.2 forgery))

/-- The actual enriched native source observed as an encoding collision is exactly its local
coin-free replay. Full failures and selected bottom results are preserved by the observation. -/
theorem runWithKeys_encodingObservation_eq
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S) :
    encodingCollisionObservation hash family <$> runWithKeys hash family sampling adv pk sk =
      encodingReplayWithKeys hash family sampling qs adv pk (eraseUpperCoins sk)
        (fun p => (upperResults hash family sampling.internal sk p).output) := by
  unfold encodingReplayWithKeys
  change _ = (do
    let result ← (simulateQ (sourceEncodingSigningOracles
      (familyEncodingProblem hash family sampling qs) sk.seed hash (eraseUpperCoins sk)
      (fun p => (upperResults hash family sampling.internal sk p).output)) (adv.forge pk)).run
        (SyncSignatureUnforgeability.emptyHistory, upperLedger hash family sampling.internal sk)
    pure (FamilyEncoding.valid family pk.seed result.2.2
      (selectEncodingCandidate hash family pk.seed result.2.2 result.1)))
  have hproj := native_run_encoding_projection hash family sampling qs sk (adv.forge pk)
    (SyncSignatureUnforgeability.emptyHistory, [])
  simp only [bottomLedger, List.map_nil, List.append_nil] at hproj
  rw [← hproj]
  simp [runWithKeys, encodingCollisionObservation, encodingLedger, upperLedger,
    upperLedgerFromResults, bottomLedger, map_eq_bind_pure_comp, bind_assoc, Prod.map]

/-- Direct source encoding observation after the actual independent full-result key sampling. -/
noncomputable def encodingReplay [SampleableType H]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let starts ← sampleStarts S
  let upper ← sampleUpperResults hash family sampling.internal pp starts sampling.sampleInternal
  let generated := keys hash pp starts (fun _ => ())
  encodingReplayWithKeys hash family sampling qs adv generated.1 generated.2
    (fun p => (upper p).output)

/-- Actual source key generation and first-request interaction factor through the local joint
fixed-coin pushforward. No whole-experiment correspondence is assumed as an input. -/
theorem sourceProgram_encodingObservation_eq [SampleableType H]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S) :
    encodingCollisionObservation hash family <$> sourceProgram hash family sampling adv =
      encodingReplay hash family sampling qs adv := by
  unfold sourceProgram encodingReplay
  simp only [map_bind, runWithKeys_encodingObservation_eq hash family sampling qs adv]
  unfold keygen
  simp only [bind_assoc]
  apply bind_congr
  intro pp
  apply bind_congr
  intro starts
  rw [← map_sampleUpperCoins_eq_sampleUpperResults]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

/-- The named adaptive reduction uses one family game for all layers and all first requests. -/
noncomputable def encodingTargetCollisionReduction [SampleableType H]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S) :
    FamilyEncoding.Adversary (familyEncodingProblem hash family sampling qs) where
  find pp := do
    let starts ← OracleComp.liftComp (sampleStarts (H := H) S) _
    let generated := keys hash pp starts (fun _ => ())
    let upper ← registerUpper hash generated.2
    let ledger := upperLedgerFromResults (M := M) hash generated.2 upper
    let (forgery, state) ←
      (simulateQ (encodingSigningOracles hash generated.2 upper) (adv.forge generated.1)).run
        (SyncSignatureUnforgeability.emptyHistory, ledger)
    pure (selectEncodingCandidate hash family pp state.2 forgery)

/-- The complete real family experiment is exactly the native source encoding observation replay.
The only resource premise is the actual source signing-query bound. -/
theorem familyExperiment_eq_encodingReplay [SampleableType H]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    FamilyEncoding.experiment (encodingTargetCollisionReduction hash family sampling qs adv) =
      encodingReplay hash family sampling qs adv := by
  unfold FamilyEncoding.experiment encodingTargetCollisionReduction encodingReplay
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind,
    simulateQ_pure, StateT.run_pure]
  simp only [familyOuter_liftStarts]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply congrArg (fun f : PP → ProbComp Bool => hash.thf.seedGen >>= f)
  funext pp
  apply congrArg
    (fun f : (OTSPosition S → Fin S.v → H) → ProbComp Bool => sampleStarts S >>= f)
  funext starts
  rw [run_registerUpper_fromResults hash family sampling qs pp starts]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply bind_congr
  intro results
  let generated := keys hash pp starts (fun _ => ())
  let upper := fun p => (results p).output
  let ledger := upperLedgerFromResults (M := M) hash generated.2 upper
  have hmatch : EncodingHistoryMatches (SyncSignatureUnforgeability.emptyHistory, ledger) :=
    encodingHistoryMatches_initial hash generated.2 upper
  have hspace : ledger.length + qs ≤
      (familyEncodingProblem hash family sampling qs).numRecords := by
    simp [ledger, familyEncodingProblem, Nat.add_comm]
  rw [nestedEncoding_run_eq_source (familyEncodingProblem hash family sampling qs) pp hash
    generated.2 upper (adv.forge generated.1) qs (hbound generated.1)
    (SyncSignatureUnforgeability.emptyHistory, ledger) hmatch hspace]
  simp [encodingReplayWithKeys, generated, upper, ledger, familyEncodingProblem, keys,
    map_eq_bind_pure_comp, bind_assoc]

/-- The actual source encoding-collision experiment equals the named family reduction experiment. -/
theorem sourceEncodingExperiment_eq_familyExperiment [SampleableType H]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    encodingCollisionObservation hash family <$> sourceProgram hash family sampling adv =
      FamilyEncoding.experiment (encodingTargetCollisionReduction hash family sampling qs adv) := by
  rw [sourceProgram_encodingObservation_eq hash family sampling qs adv,
    familyExperiment_eq_encodingReplay hash family sampling qs adv hbound]

/-- Native returned mass of the complete actual source encoding-collision observation. -/
noncomputable def encodingCollisionMass [SampleableType H]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) : ℝ≥0∞ :=
  𝒟[encodingCollisionObservation hash family <$> sourceProgram hash family sampling adv] {true}

/-- The actual mixed-family reduction has exactly the native source encoding-collision mass,
with the sharp eager cap `qs + upperCount S` and no component multiplier. -/
theorem encodingCollisionMass_eq_familyAdvantage [SampleableType H]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    encodingCollisionMass hash family sampling adv =
      FamilyEncoding.advantage (encodingTargetCollisionReduction hash family sampling qs adv) := by
  unfold encodingCollisionMass FamilyEncoding.advantage FamilyEncoding.outputMeasure
  rw [sourceEncodingExperiment_eq_familyExperiment hash family sampling qs adv hbound]

/-- The actual selected-component encoding flag is covered by the reduction's concrete scan. -/
theorem sourceEncodingCollision_implies_observation
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Result PP H M R Coins S) (hseed : out.pk.seed = out.sk.seed)
    (h : Unforgeability.sourceEncodingCollision hash family out = true) :
    encodingCollisionObservation hash family out = true := by
  cases hdecoded : Unforgeability.sourceDecoded? hash family out with
  | none => simp [Unforgeability.sourceEncodingCollision, hdecoded] at h
  | some decoded =>
    rcases decoded with ⟨candidate, word⟩
    cases href : referenceAt hash out candidate.position with
    | none => simp [Unforgeability.sourceEncodingCollision, hdecoded, href] at h
    | some reference =>
      cases hresult : reference.result with
      | none => simp [Unforgeability.sourceEncodingCollision, hdecoded, href, hresult] at h
      | some wr =>
        have hconditions : wr.1 = word ∧
            ((⟨reference.position, reference.message⟩ : FamilyEncoding.Query M H S), wr.2) ≠
              ((⟨candidate.position, candidate.message⟩ : FamilyEncoding.Query M H S),
                candidate.signature.randomizer) := by
          simpa only [Unforgeability.sourceEncodingCollision, hdecoded, href, hresult,
            decide_eq_true_eq] using h
        obtain ⟨hsource, hword⟩ := Unforgeability.sourceDecoded?_spec hash family out
          candidate word hdecoded
        have hcandidate : FamilyEncoding.valid family out.pk.seed (encodingLedger hash out)
            (candidateEncoding candidate) = true :=
          FamilyEncoding.valid_of_record family out.pk.seed (encodingLedger hash out)
            (candidateEncoding candidate) reference
            (referenceAt_mem_encodingLedger hash out candidate.position reference href)
            (by simpa only [candidateEncoding, hseed] using hword)
            (by simpa only [← hconditions.1] using hresult)
            (referenceAt_position hash out candidate.position reference href) hconditions.2
        have hmem : candidateEncoding candidate ∈
            encodingCandidates hash family out.pk.seed out.forgery := by
          rw [hseed]
          exact candidateAt_mem_encodingCandidates hash family out.sk.seed out.forgery _ _ candidate
            hsource
        exact selectEncodingCandidate_valid_of_mem hash family out.pk.seed
          (encodingLedger hash out) out.forgery (candidateEncoding candidate) hmem hcandidate

/-- The native strong-source encoding flag is bounded by the one actual mixed-family experiment. -/
theorem sourceEncodingBad_mass_le_familyAdvantage [SampleableType H]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (adv : SchemeAdversary PP H M R S)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    𝒟[Unforgeability.sourceEncodingBad hash family sampling <$>
      sourceProgram hash family sampling adv] {true} ≤
      FamilyEncoding.advantage (encodingTargetCollisionReduction hash family sampling qs adv) := by
  rw [← encodingCollisionMass_eq_familyAdvantage hash family sampling qs adv hbound]
  unfold encodingCollisionMass
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (sourceProgram hash family sampling adv)
    (fun out => pure (Unforgeability.sourceEncodingBad hash family sampling out))
    (fun out => pure (encodingCollisionObservation hash family out)) (measurableSet_singleton true)
  intro out hout
  by_cases hbad : Unforgeability.sourceEncodingBad hash family sampling out = true
  · have hcollision : Unforgeability.sourceEncodingCollision hash family out = true := by
      have hbad' := hbad
      simp only [Unforgeability.sourceEncodingBad, Bool.and_eq_true] at hbad'
      exact hbad'.2
    have htarget := sourceEncodingCollision_implies_observation hash family out
      (sourceProgram_support_seed_eq hash family sampling adv out hout) hcollision
    simp [hbad, htarget]
  · have hfalse : Unforgeability.sourceEncodingBad hash family sampling out = false := by
      cases hcase : Unforgeability.sourceEncodingBad hash family sampling out <;> simp_all
    simp [hfalse]


end GXMSS.Hypertree.Security
