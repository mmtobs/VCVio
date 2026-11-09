/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Reductions.EncodingCollision
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Mixed-family history and native-attempt controls

Different retry budgets and samplers distinguish bottom from internal requests. The native logger
retains successful bottom metadata even when the full signature callback returns failure.
-/

public section

namespace GXMSS.Hypertree.Security.FamilyEncodingProbe

open Encoding FamilyEncoding

/-- Two one-leaf layers, with one global epoch and one fixed upper certificate. -/
@[expose, reducible] def shape : Shape := ⟨2, 0, 1, 1, by decide⟩

/-- The singleton encoding word. -/
@[expose] def word : Codeword shape.v (2 ^ shape.w) := fun _ => 0

/-- All coordinates accept true randomizers and reject false randomizers. -/
@[expose] def family : EncodingFamily Unit Bool Bool Unit shape where
  component _ :=
    { code := {word}
      incomparable := by
        intro x hx y hy hne
        exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
      encode _ _ r _ := if r then some ⟨word, Set.mem_singleton _⟩ else none }

/-- Two failed bottom attempts and one successful internal attempt use separate actual samplers. -/
@[expose] def sampling : RetrySampling Bool where
  bottom := RetryPlan.iid Bool 2
  internal := RetryPlan.iid Bool 1
  sampleBottom := pure (fun _ => false)
  sampleInternal := pure (fun _ => true)

/-- A capacity of two allows one upper record and one bottom request. -/
@[expose] def problem : Problem Unit Bool Unit Bool shape :=
  ⟨family, sampling, pure (), 2⟩

/-- A bottom application-message request. -/
@[expose] def bottomQuery : Query Bool Unit shape :=
  ⟨bottomPosition shape 0, bottomMessage 0 true⟩

/-- An internal digest request with its own message fibre. -/
@[expose] def upperQuery : Query Bool Unit shape :=
  ⟨(upperPositionAt shape 0 ⟨0, by decide⟩).1,
    internalMessage (upperPositionAt shape 0 ⟨0, by decide⟩) ()⟩

/-- Bottom retry exhaustion is a returned result under its two-attempt plan. -/
theorem bottom_exhaustion : sampleResult problem () bottomQuery = pure none := rfl

/-- Internal requests use the one-attempt sampler rather than the bottom sampler. -/
theorem internal_success : sampleResult problem () upperQuery = pure (some (word, true)) := rfl

/-- Exhausted bottom requests consume their full coordinate. -/
theorem exhausted_coordinate_used :
    used (R := Bool) (finish 2 [] bottomQuery none).2 bottomQuery.1 = true := by decide

/-- A failed record cannot be replaced by a later message at the same coordinate. -/
theorem duplicate_retains_failure :
    finish 2 [⟨bottomQuery.1, bottomQuery.2, none⟩]
      ⟨bottomQuery.1, bottomMessage 0 false⟩ (some (word, true)) =
      (none, [⟨bottomQuery.1, bottomQuery.2, none⟩]) := rfl

/-- Exact message/randomizer replay fails the collision test. -/
theorem exact_pair_replay :
    valid family () [⟨bottomQuery.1, bottomQuery.2, some (word, true)⟩]
      ⟨bottomQuery, true⟩ = false := by decide

/-- A different application message with the same successful word is pair-fresh. -/
theorem changed_message_collision :
    valid family () [⟨bottomQuery.1, bottomQuery.2, some (word, true)⟩]
      ⟨⟨bottomQuery.1, bottomMessage 0 false⟩, true⟩ = true := by decide

/-- An internal record cannot stand in for a bottom record with the same word. -/
theorem distinct_coordinate_rejected :
    valid family () [⟨upperQuery.1, upperQuery.2, some (word, true)⟩]
      ⟨bottomQuery, true⟩ = false := by decide

/-- Actual deterministic first-success metadata at the second attempt. -/
@[expose] def successfulAttempt (_ : Epoch shape) (msg : Bool) (coins : Fin 2 → Bool) :=
  (RetryPlan.iid Bool 2).run (family.component (bottomPosition shape 0)) ()
    (bottomMessage 0 msg) () coins

/-- A private logger with successful bottom retry and an exhausted full-signature continuation. -/
@[expose] def failedContinuation :=
  signingOracleWithAttempts (pure (fun i : Fin 2 => i.val == 1)) successfulAttempt
    (fun _ _ _ => (none : Option (Signature Bool Unit shape)))

/-- The full failure still records the selected bottom word, second attempt and consumed prefix. -/
theorem bottom_success_before_full_failure :
    (failedContinuation (0, true)).run (SyncSignatureUnforgeability.emptyHistory, []) =
      pure (none,
        Function.update SyncSignatureUnforgeability.emptyHistory 0 (some (true, none)),
        [⟨0, true, .success word true 2 [false, true]⟩]) := rfl

/-- A failed full-signature request remains consumed and does not append another attempt. -/
theorem duplicate_full_failure_keeps_attempt :
    (failedContinuation (0, false)).run
        (Function.update SyncSignatureUnforgeability.emptyHistory 0 (some (true, none)),
          [⟨0, true, .success word true 2 [false, true]⟩]) =
      pure (none,
        Function.update SyncSignatureUnforgeability.emptyHistory 0 (some (true, none)),
        [⟨0, true, .success word true 2 [false, true]⟩]) := rfl

/-- One upper success and one bottom exhaustion occupy both slots of the mixed cap. -/
theorem mixed_cap_counts_exhaustion :
    (finish 2 (finish 2 [] upperQuery (some (word, true))).2 bottomQuery none).2.length = 2 := by
  decide

/-- Observing optional bottom data retains the successful word after the full-signature failure. -/
theorem successful_bottom_observation :
    bottomLedger (H := Unit) [⟨0, true, .success word true 2 [false, true]⟩] =
      [⟨bottomQuery.1, bottomQuery.2, some (word, true)⟩] := rfl

example := @sourceProgram_map_eq_interaction
example := @sourceProgram_attempts_match_history
example := @keygen_map_keyObservation
example := @sourceProgram_bottomAttempts_nodup
example := @sourceEncodingBad_mass_le_familyAdvantage
noncomputable example := @encodingTargetCollisionReduction

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``sourceProgram_map_eq_interaction,
    ``sourceProgram_attempts_match_history,
    ``keygen_map_keyObservation,
    ``sourceProgram_bottomAttempts_nodup,
    ``sourceEncodingExperiment_eq_familyExperiment,
    ``encodingCollisionMass_eq_familyAdvantage,
    ``sourceEncodingBad_mass_le_familyAdvantage,
    ``run_encodingQuery_mOfFn,
    ``bottom_success_before_full_failure,
    ``duplicate_full_failure_keeps_attempt,
    ``mixed_cap_counts_exhaustion,
    ``distinct_coordinate_rejected]

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncoding,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction,
      `HashSig.GXMSS.Security.Hypertree.Reductions.EncodingCollision]
    #[(``sourceProgram_map_eq_interaction,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction),
      (``sourceProgram_attempts_match_history,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction),
      (``keygen_map_keyObservation,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction),
      (``sourceEncodingExperiment_eq_familyExperiment,
        `HashSig.GXMSS.Security.Hypertree.Reductions.EncodingCollision),
      (``sourceEncodingBad_mass_le_familyAdvantage,
        `HashSig.GXMSS.Security.Hypertree.Reductions.EncodingCollision)]
    #[]
    #[(``encodingTargetCollisionReduction,
        `HashSig.GXMSS.Security.Hypertree.Reductions.EncodingCollision),
      (``FamilyEncoding.challengeOracle,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncoding)]

end GXMSS.Hypertree.Security.FamilyEncodingProbe
