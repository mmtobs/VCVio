/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Scheme
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Mixed-coordinate encoding target collisions

The challenge domain contains complete one-time-key coordinates and their actual message fibres.
Bottom and internal coordinates use their captured retry plans and samplers. Every eligible query
occupies one slot even after exhaustion; repeated coordinates are rejected before sampling.
-/

public section

namespace GXMSS.Hypertree.Security.FamilyEncoding

open Encoding OracleComp OracleSpec
open scoped ENNReal

/-- A complete coordinate and a message in its own fibre. -/
abbrev Query (M H : Type) (S : Shape) := (p : OTSPosition S) × Message S M H p

instance {M H : Type} {S : Shape} [DecidableEq M] [DecidableEq H] :
    DecidableEq (Query M H S) := by
  let : (p : OTSPosition S) → DecidableEq (Message S M H p) := fun p => by
    dsimp [Message]
    split_ifs <;> infer_instance
  exact inferInstanceAs (DecidableEq (Sigma _))

/-- One consumed coordinate, including its first message and optional selected encoding result. -/
structure Record (M H R : Type) (S : Shape) where
  /-- The full one-time-key coordinate consumed by the request. -/
  position : OTSPosition S
  /-- The first message supplied at that coordinate. -/
  message : Message S M H position
  /-- First successful word/randomizer pair, or explicit exhaustion. -/
  result : Option (Codeword S.v (2 ^ S.w) × R)

/-- Ordered eligible requests; failed requests remain occupied records. -/
abbrev Transcript (M H R : Type) (S : Shape) := List (Record M H R S)

/-- A candidate message and explicit randomizer at one complete coordinate. -/
structure Forgery (M H R : Type) (S : Shape) where
  /-- The candidate coordinate and message. -/
  query : Query M H S
  /-- The candidate randomizer. -/
  randomizer : R

variable {PP M H R : Type} {S : Shape}

/-- Family, actual coin samplers, public seed sampler and total consumed-record capacity. -/
structure Problem (PP M H R : Type) (S : Shape) where
  /-- One incomparable code per complete coordinate and message fibre. -/
  family : EncodingFamily PP M R H S
  /-- Separate bottom/internal plans and coin distributions. -/
  sampling : RetrySampling R
  /-- One common public-parameter draw. -/
  paramGen : ProbComp PP
  /-- Capacity counts all eligible records, including exhaustion. -/
  numRecords : ℕ

/-- Select the configured plan and actual sampler according to the coordinate's message kind. -/
@[expose] def sampleResult (prob : Problem PP M H R S) (pp : PP) (q : Query M H S) :
    ProbComp (Option (Codeword S.v (2 ^ S.w) × R)) :=
  if q.1.1.1.val = 0 then
    (fun coins => (prob.sampling.bottom.run (prob.family.component q.1) pp q.2 () coins).output)
      <$> prob.sampling.sampleBottom
  else
    (fun coins => (prob.sampling.internal.run (prob.family.component q.1) pp q.2 () coins).output)
      <$> prob.sampling.sampleInternal

/-- Whether this coordinate has already consumed its first-request slot. -/
@[expose] def used (transcript : Transcript M H R S) (position : OTSPosition S) : Bool :=
  transcript.any fun entry => decide (entry.position = position)

/-- Repeated coordinates and requests beyond the total cap are rejected. -/
@[expose] def rejected (cap : ℕ) (transcript : Transcript M H R S)
    (position : OTSPosition S) : Bool :=
  decide (cap ≤ transcript.length) || used transcript position

/-- Commit an eligible result, including exhaustion, without changing a rejected history. -/
@[expose] def finish (cap : ℕ) (transcript : Transcript M H R S) (q : Query M H S)
    (answer : Option (Codeword S.v (2 ^ S.w) × R)) :
    Option (Codeword S.v (2 ^ S.w) × R) × Transcript M H R S :=
  if rejected cap transcript q.1 then (none, transcript)
  else (answer, transcript ++ [⟨q.1, q.2, answer⟩])

/-- An exhausted eligible query consumes its coordinate and preserves its message. -/
theorem finish_none_of_eligible (cap : ℕ) (transcript : Transcript M H R S)
    (q : Query M H S) (h : rejected cap transcript q.1 = false) :
    finish cap transcript q none = (none, transcript ++ [⟨q.1, q.2, none⟩]) := by
  simp [finish, h]

/-- Every eligible completed request marks its coordinate used, including returned failure. -/
theorem used_finish_of_eligible (cap : ℕ) (transcript : Transcript M H R S)
    (q : Query M H S) (answer : Option (Codeword S.v (2 ^ S.w) × R))
    (h : rejected cap transcript q.1 = false) :
    used (finish cap transcript q answer).2 q.1 = true := by
  simp [finish, h, used]

/-- A consumed coordinate is rejected for every later message. -/
theorem rejected_of_used (cap : ℕ) (transcript : Transcript M H R S)
    (position : OTSPosition S) (h : used transcript position = true) :
    rejected cap transcript position = true := by simp [rejected, h]

/-- Rejection preserves the entire previous transcript. -/
theorem finish_of_rejected (cap : ℕ) (transcript : Transcript M H R S)
    (q : Query M H S) (answer : Option (Codeword S.v (2 ^ S.w) × R))
    (h : rejected cap transcript q.1 = true) :
    finish cap transcript q answer = (none, transcript) := by
  simp [finish, h]

/-- Completed transitions preserve the total record bound. -/
theorem length_finish_le (cap : ℕ) (transcript : Transcript M H R S)
    (q : Query M H S) (answer : Option (Codeword S.v (2 ^ S.w) × R))
    (h : transcript.length ≤ cap) : (finish cap transcript q answer).2.length ≤ cap := by
  unfold finish
  split_ifs with hr
  · exact h
  · have hcap : transcript.length < cap := by
      have h' : cap > transcript.length ∧ used transcript q.1 = false := by
        simpa [rejected] using hr
      exact h'.1
    simpa using Nat.succ_le_of_lt hcap

/-- The challenge returns only the selected optional word/randomizer pair. -/
abbrev challengeSpec (M H R : Type) (S : Shape) : OracleSpec (Query M H S) :=
  (Query M H S) →ₒ Option (Codeword S.v (2 ^ S.w) × R)

/-- Reject before drawing coins; append exactly one record on every eligible returned path. -/
@[expose] def challengeOracle (prob : Problem PP M H R S) (pp : PP) :
    QueryImpl (challengeSpec M H R S) (StateT (Transcript M H R S) ProbComp) := fun q => do
  let transcript ← get
  if rejected prob.numRecords transcript q.1 then return none
  else
    let answer ← (sampleResult prob pp q : StateT (Transcript M H R S) ProbComp _)
    let result := finish prob.numRecords transcript q answer
    set result.2
    return result.1

/-- Rejection draws no coins and leaves the consumed-coordinate history unchanged. -/
theorem challengeOracle_run_of_rejected (prob : Problem PP M H R S) (pp : PP)
    (q : Query M H S) (transcript : Transcript M H R S)
    (h : rejected prob.numRecords transcript q.1 = true) :
    (challengeOracle prob pp q).run transcript = pure (none, transcript) := by
  simp [challengeOracle, h]

/-- An eligible call records its optional result, including exhaustion, exactly once. -/
theorem challengeOracle_run_of_eligible (prob : Problem PP M H R S) (pp : PP)
    (q : Query M H S) (transcript : Transcript M H R S)
    (h : rejected prob.numRecords transcript q.1 = false) :
    (challengeOracle prob pp q).run transcript =
      (fun answer => (answer, transcript ++ [⟨q.1, q.2, answer⟩])) <$>
        sampleResult prob pp q := by
  simp [challengeOracle, h, finish, map_eq_bind_pure_comp]

/-- Every returned selected pair is an actual success in that coordinate's message fibre. -/
theorem value_eq_some_of_mem_sampleResult (prob : Problem PP M H R S) (pp : PP)
    (q : Query M H S) {word : Codeword S.v (2 ^ S.w)} {r : R}
    (h : some (word, r) ∈ support (sampleResult prob pp q)) :
    prob.family.value q.1 pp q.2 r = some word := by
  unfold sampleResult at h
  split_ifs at h with hkind
  · exact prob.sampling.bottom.value_eq_some_of_mem_sampled_output
      (prob.family.component q.1) pp q.2 () prob.sampling.sampleBottom h
  · exact prob.sampling.internal.value_eq_some_of_mem_sampled_output
      (prob.family.component q.1) pp q.2 () prob.sampling.sampleInternal h

/-- Ambient randomness passes through; encoding challenges use the mixed family handler. -/
@[expose] def oracles (prob : Problem PP M H R S) (pp : PP) :
    QueryImpl (unifSpec + challengeSpec M H R S)
      (StateT (Transcript M H R S) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Transcript M H R S) ProbComp) +
    challengeOracle prob pp

/-- Every retained successful record includes its actual encoding equation. Exhausted records
remain in the transcript and impose no successful-value equation. -/
@[expose] def WellFormed (family : EncodingFamily PP M R H S) (pp : PP)
    (transcript : Transcript M H R S) : Prop :=
  ∀ entry ∈ transcript, ∀ word r, entry.result = some (word, r) →
    family.value entry.position pp entry.message r = some word

/-- The complete challenge handler preserves successful-record equations under adaptive use. -/
theorem oracles_preserves_wellFormed (prob : Problem PP M H R S) (pp : PP) :
    QueryImpl.PreservesInv (oracles prob pp) (WellFormed prob.family pp) := by
  intro q transcript hformed out hout
  cases q with
  | inl random =>
    have hrun : (oracles prob pp (.inl random)).run transcript =
        (fun answer => (answer, transcript)) <$> (unifSpec.query random : ProbComp _) := by
      rfl
    rw [hrun] at hout
    obtain ⟨_, _, heq⟩ := OracleComp.mem_support_map_peel _ _ hout
    cases heq
    exact hformed
  | inr query =>
    by_cases hreject : rejected prob.numRecords transcript query.1 = true
    · have hrun := challengeOracle_run_of_rejected prob pp query transcript hreject
      change out ∈ support ((challengeOracle prob pp query).run transcript) at hout
      rw [hrun] at hout
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      exact hformed
    · have heligible : rejected prob.numRecords transcript query.1 = false := by
        simpa using hreject
      change out ∈ support ((challengeOracle prob pp query).run transcript) at hout
      rw [challengeOracle_run_of_eligible prob pp query transcript heligible] at hout
      obtain ⟨answer, hanswer, heq⟩ := OracleComp.mem_support_map_peel _ _ hout
      cases heq
      intro entry hentry word r hresult
      rcases List.mem_append.mp hentry with hold | hnew
      · exact hformed entry hold word r hresult
      · have heq : entry = (⟨query.1, query.2, answer⟩ : Record M H R S) := by
          simpa using hnew
        subst entry
        exact value_eq_some_of_mem_sampleResult prob pp query (hresult ▸ hanswer)

/-- Whole adaptive runs preserve every successful encoding equation, including runs that also
contain exhausted first requests. Missing execution mass is unchanged. -/
theorem run_preserves_wellFormed (prob : Problem PP M H R S) (pp : PP) {α : Type}
    (program : OracleComp (unifSpec + challengeSpec M H R S) α)
    (transcript : Transcript M H R S) (hformed : WellFormed prob.family pp transcript)
    (out : α × Transcript M H R S)
    (hout : out ∈ support ((simulateQ (oracles prob pp) program).run transcript)) :
    WellFormed prob.family pp out.2 :=
  OracleComp.simulateQ_run_preservesInv (oracles prob pp) (WellFormed prob.family pp)
    (oracles_preserves_wellFormed prob pp) program transcript hformed out hout

/-- A fully adaptive family-encoding adversary. -/
structure Adversary (prob : Problem PP M H R S) where
  /-- The candidate may depend on all previous returned failures and successes. -/
  find : PP → OracleComp (unifSpec + challengeSpec M H R S) (Forgery M H R S)

/-- Exact same-coordinate, same-word and distinct-message/randomizer-pair target collision. -/
@[expose] def valid [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (family : EncodingFamily PP M R H S) (pp : PP) (transcript : Transcript M H R S)
    (candidate : Forgery M H R S) : Bool :=
  match family.value candidate.query.1 pp candidate.query.2 candidate.randomizer with
  | none => false
  | some word => transcript.any fun entry =>
      match entry.result with
      | none => false
      | some (target, r) => decide (entry.position = candidate.query.1 ∧ target = word ∧
          ((⟨entry.position, entry.message⟩ : Query M H S), r) ≠
            (candidate.query, candidate.randomizer))

/-- A concrete successful, pair-fresh record witnesses the exact family collision predicate. -/
theorem valid_of_record [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (family : EncodingFamily PP M R H S) (pp : PP) (transcript : Transcript M H R S)
    (candidate : Forgery M H R S) (entry : Record M H R S)
    (hentry : entry ∈ transcript) {word : Codeword S.v (2 ^ S.w)} {r : R}
    (hcandidate : family.value candidate.query.1 pp candidate.query.2 candidate.randomizer =
      some word) (hresult : entry.result = some (word, r))
    (hposition : entry.position = candidate.query.1)
    (hfresh : ((⟨entry.position, entry.message⟩ : Query M H S), r) ≠
      (candidate.query, candidate.randomizer)) : valid family pp transcript candidate = true := by
  simp only [valid, hcandidate, List.any_eq_true]
  refine ⟨entry, hentry, ?_⟩
  simp [hresult, hposition, hfresh]

/-- An exhausted record cannot witness a collision, regardless of its consumed position. -/
theorem valid_singleton_exhausted [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (family : EncodingFamily PP M R H S) (pp : PP) (q : Query M H S)
    (candidate : Forgery M H R S) :
    valid family pp [⟨q.1, q.2, none⟩] candidate = false := by
  unfold valid
  cases family.value candidate.query.1 pp candidate.query.2 candidate.randomizer <;> rfl

/-- The complete mixed-family experiment under the actual seed and coin samplers. -/
@[expose] def experiment [DecidableEq M] [DecidableEq H] [DecidableEq R]
    {prob : Problem PP M H R S} (adv : Adversary prob) : ProbComp Bool := do
  let pp ← prob.paramGen
  let (candidate, transcript) ← (simulateQ (oracles prob pp) (adv.find pp)).run []
  return valid prob.family pp transcript candidate

/-- Successful-output measure, with no conditioning on returned success. -/
@[expose] noncomputable def outputMeasure [DecidableEq M] [DecidableEq H] [DecidableEq R]
    {prob : Problem PP M H R S} (adv : Adversary prob) : MeasureTheory.Measure Bool :=
  𝒟[experiment adv]

/-- The returned winning mass of the complete adaptive family experiment. -/
@[expose] noncomputable def advantage [DecidableEq M] [DecidableEq H] [DecidableEq R]
    {prob : Problem PP M H R S} (adv : Adversary prob) : ℝ≥0∞ := outputMeasure adv {true}

end GXMSS.Hypertree.Security.FamilyEncoding
