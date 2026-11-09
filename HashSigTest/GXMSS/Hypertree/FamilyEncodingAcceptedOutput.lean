/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncodingAcceptedOutput
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Mixed accepted-output counter controls

A constant decoder in each fibre is injective only on that fibre's singleton accepted set. The
bottom and internal singleton codes have comparable words across coordinates. Different bounded
counter plans exercise wraparound first success and occupied exhaustion under the actual native
hash challenge. Complete adaptive transcript transport is applied to a program observing failure.
-/

public section

namespace GXMSS.Hypertree.Security.FamilyEncodingAcceptedOutputProbe

open Encoding OracleComp OracleSpec FamilyEncodingAcceptedOutput

/-- Two one-leaf layers with different application and internal message fibres. -/
@[expose, reducible] def shape : Shape := ⟨2, 0, 1, 1, by decide⟩

/-- Comparable singleton words belong to distinct coordinate-local codes. -/
@[expose] def word (p : OTSPosition shape) : Codeword shape.v (2 ^ shape.w) :=
  fun _ => if p.1.1.val = 0 then 0 else 1

/-- Each coordinate accepts a single digest, independently of its constant public decoder. -/
@[expose] def accepts (p : OTSPosition shape) (y : Fin 4) : Bool :=
  decide (y = if p.1.1.val = 0 then 0 else 1)

/-- The hash exposes the randomizer as its full output; public decoding drops all its bits. -/
@[expose] def hash : HashFamily Unit Bool Unit (Fin 4) (Fin 4) shape where
  eval _ _ r := r
  accepts := accepts
  word p _ := word p

/-- Singleton codes require no cross-coordinate incomparability law. -/
@[expose] def family : EncodingFamily Unit Bool (Fin 4) Unit shape where
  component p :=
    { code := {word p}
      incomparable := by
        intro x hx y hy hne
        exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
      encode _ _ r _ := if accepts p r then some ⟨word p, Set.mem_singleton _⟩ else none }

/-- Correlated plans with different budgets: bottom wraps to success; internal exhausts. -/
@[expose, reducible] def sampling : RetrySampling (Fin 4) where
  bottom := RetryPlan.counter 4 3 (by decide)
  internal := RetryPlan.counter 4 2 (by decide)
  sampleBottom := pure 3
  sampleInternal := pure 2

/-- The primitive uses these actual counter laws and a two-record consumed-coordinate cap. -/
@[expose, reducible] def problem : Problem Unit Bool Unit (Fin 4) (Fin 4) shape :=
  ⟨hash, sampling, pure (), 2⟩

/-- Restricted accepted-set injectivity supports the bridge despite a constant global decoder. -/
@[expose, reducible] def bridge : AcceptedBridge Unit Bool Unit (Fin 4) (Fin 4) shape where
  problem := problem
  family := family
  word_injOn p first hfirst second hsecond _ := by
    have hfirst' : first = if p.1.1.val = 0 then 0 else 1 := of_decide_eq_true hfirst
    have hsecond' : second = if p.1.1.val = 0 then 0 else 1 := of_decide_eq_true hsecond
    exact hfirst'.trans hsecond'.symm
  value_eq pp q r := by
    dsimp [Family.value, family, IncomparableEncoding.value, problem, hash]
    by_cases h : accepts q.1 r = true <;> simp [h]

/-- Actual bottom application-message query. -/
@[expose] def bottomQuery : FamilyEncoding.Query Bool Unit shape :=
  ⟨bottomPosition shape 0, bottomMessage 0 true⟩

/-- Internal digest query, with its separate singleton message fibre. -/
@[expose] def upperQuery : FamilyEncoding.Query Bool Unit shape :=
  ⟨(upperPositionAt shape 0 ⟨0, by decide⟩).1,
    internalMessage (upperPositionAt shape 0 ⟨0, by decide⟩) ()⟩

/-- The decoder is globally noninjective, so a global decoder premise would reject this bridge. -/
theorem decoder_not_globally_injective : ¬ Function.Injective (hash.word bottomQuery.1) := by
  intro hinj
  exact (by decide : (0 : Fin 4) ≠ 1) (hinj (show hash.word bottomQuery.1 0 =
    hash.word bottomQuery.1 1 from rfl))

/-- Comparable words at bottom and internal coordinates do not violate fibrewise assumptions. -/
theorem cross_coordinate_words_comparable :
    ¬ IncomparableWords (word bottomQuery.1) (word upperQuery.1) := by
  simp [IncomparableWords, word, bottomQuery, upperQuery, shape,
    bottomPosition, upperPositionAt, positionAt]

/-- Native full hash search wraps from three to zero and stops before its third attempt. -/
theorem counter_full_metadata :
    fullResult hash sampling.bottom () bottomQuery 3 = .success 0 2 [3, 0] := rfl

/-- The internal plan exhausts after both correlated attempts. -/
theorem internal_full_exhaustion :
    fullResult hash sampling.internal () upperQuery 2 = .exhausted [2, 3] := rfl

/-- Decoding the native full result retains the exact successful attempt and consumed prefix. -/
theorem decoded_full_metadata :
    sampling.bottom.run (family.component bottomQuery.1) () bottomQuery.2 () 3 =
      .success (word bottomQuery.1) 0 2 [3, 0] := rfl

/-- Native challenge returns the accepted randomizer, without replacing it by a decoded word. -/
theorem native_counter_answer : sampleResult problem () bottomQuery = pure (some 0) := rfl

/-- An exhausted eligible internal request occupies a record and its complete coordinate. -/
theorem exhausted_native_request_consumes :
    (challengeOracle problem () upperQuery).run [] =
      pure (none, [⟨upperQuery.1, upperQuery.2, none⟩]) := rfl

/-- A repeated exhausted request does not rerun the counter or append a new record. -/
theorem repeated_exhausted_retains_history :
    (challengeOracle problem () upperQuery).run [⟨upperQuery.1, upperQuery.2, none⟩] =
      pure (none, [⟨upperQuery.1, upperQuery.2, none⟩]) := rfl

/-- Reaching the cap rejects a new coordinate before retry sampling. -/
theorem full_cap_rejects :
    (challengeOracle { problem with numRecords := 1 } () bottomQuery).run
        [⟨upperQuery.1, upperQuery.2, none⟩] =
      pure (none, [⟨upperQuery.1, upperQuery.2, none⟩]) := rfl

/-- Exhausted native histories project to exhausted source histories at the same full coordinate. -/
theorem exhausted_projection :
    decodeTranscript hash () [⟨upperQuery.1, upperQuery.2, none⟩] =
      [⟨upperQuery.1, upperQuery.2, none⟩] := rfl

/-- A native full-hash win at a bottom target uses a different message in the same fibre. -/
theorem changed_message_native_collision :
    valid hash () [⟨bottomQuery.1, bottomQuery.2, some 0⟩]
      ⟨⟨bottomQuery.1, bottomMessage 0 false⟩, 0⟩ = true := by decide

/-- The public decoder also maps an unaccepted digest to the target word. Neither game may
turn that equality into a collision without the successful source-value equation. -/
theorem unaccepted_same_word_rejected :
    hash.word bottomQuery.1 0 = hash.word bottomQuery.1 1 ∧
      valid hash () [⟨bottomQuery.1, bottomQuery.2, some 0⟩]
        ⟨⟨bottomQuery.1, bottomMessage 0 false⟩, 1⟩ = false ∧
      FamilyEncoding.valid family ()
        [⟨bottomQuery.1, bottomQuery.2, some (word bottomQuery.1, 0)⟩]
        ⟨⟨bottomQuery.1, bottomMessage 0 false⟩, 1⟩ = false := by decide

/-- A zero retry budget returns exhaustion and still occupies the eligible native coordinate. -/
theorem zero_budget_consumes :
    (challengeOracle { problem with sampling :=
      { sampling with bottom := RetryPlan.counter 4 0 (by decide), sampleBottom := pure 3 } }
      () bottomQuery).run [] = pure (none, [⟨bottomQuery.1, bottomQuery.2, none⟩]) := rfl

/-- A zero record capacity rejects before any retry sampling and retains an empty history. -/
theorem zero_cap_rejects :
    (challengeOracle { problem with numRecords := 0 } () bottomQuery).run [] =
      pure (none, []) := rfl

/-- Equal full digests at distinct complete coordinates do not witness a native collision. -/
theorem wrong_coordinate_not_collision :
    valid hash () [⟨upperQuery.1, upperQuery.2, some 0⟩] ⟨bottomQuery, 0⟩ = false := by decide

/-- A failed native record cannot witness a hash collision. -/
theorem exhausted_not_collision :
    valid hash () [⟨bottomQuery.1, bottomQuery.2, none⟩]
      ⟨⟨bottomQuery.1, bottomMessage 0 false⟩, 0⟩ = false := by decide

/-- An adaptive source program distinguishes returned exhaustion before issuing a bottom query. -/
@[expose] def adaptiveProgram :
    OracleComp (unifSpec + FamilyEncoding.challengeSpec Bool Unit (Fin 4) shape) Bool := do
  let upper ← (unifSpec + FamilyEncoding.challengeSpec Bool Unit (Fin 4) shape).query
    (.inr upperQuery)
  if upper.isNone then
    let bottom ← (unifSpec + FamilyEncoding.challengeSpec Bool Unit (Fin 4) shape).query
      (.inr bottomQuery)
    return bottom.isSome
  else return false

/-- Full adaptive transport preserves the client's answer and both ordered consumed records. -/
theorem adaptive_full_history :
    Prod.map id (decodeTranscript hash ()) <$>
        (simulateQ (oracles problem ())
          (simulateQ (bridge.liftedOracles ()) adaptiveProgram)).run [] =
      pure (true, [⟨upperQuery.1, upperQuery.2, none⟩,
        ⟨bottomQuery.1, bottomQuery.2, some (word bottomQuery.1, 0)⟩]) := by
  rw [bridge.run_decode]
  rfl

example := @AcceptedBridge.advantage_le_hash
example := @AcceptedBridge.fullResult_isFirstSuccess
example := @FamilyEncoding.run_preserves_wellFormed

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``AcceptedBridge.advantage_le_hash,
    ``AcceptedBridge.run_decode,
    ``AcceptedBridge.fullResult_eq,
    ``AcceptedBridge.valid_implies_hash_collision,
    ``AcceptedBridge.decoded_run_wellFormed,
    ``HashRetry.retryIndexed_eq_search,
    ``HashRetry.accepts_of_search_output,
    ``FamilyEncoding.run_preserves_wellFormed,
    ``adaptive_full_history,
    ``decoder_not_globally_injective,
    ``unaccepted_same_word_rejected,
    ``zero_budget_consumes,
    ``zero_cap_rejects]

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.HashRetry,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncodingAcceptedOutput]
    #[(``AcceptedBridge.advantage_le_hash,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncodingAcceptedOutput),
      (``AcceptedBridge.run_decode,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncodingAcceptedOutput)]
    #[]
    #[(``AcceptedBridge.reduction,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncodingAcceptedOutput),
      (``challengeOracle,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncodingAcceptedOutput),
      (``HashRetry.search, `HashSig.GXMSS.Security.Hypertree.Auxiliary.HashRetry)]

end GXMSS.Hypertree.Security.FamilyEncodingAcceptedOutputProbe
