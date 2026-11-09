/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Accepted-output encoding-bridge controls

A constant word map is injective on a singleton accepted set while collapsing rejected outputs.
A forged transcript demonstrates why accepted-output transport must retain actual encoder success.
-/

public section

namespace GXMSS.Encoding.AcceptedBridgeProbe

open TargetCollisionResistance TargetCollisionTransport TweakableHash

/-- A one-word code. -/
@[expose] def word : Codeword 1 2 := fun _ => 0

/-- Exactly one hash output is accepted. -/
@[expose] def accepts (y : Option Bool) : Bool := decide (y = some false)

/-- The tag is ignored by the hash, while the optional Boolean is its actual output. -/
@[expose] def th : TweakableHash Unit Unit ((Bool × Option Bool) × Unit) (Option Bool) where
  seedGen := pure ()
  eval _ _ pair := pair.1.2

/-- Failed hash outputs return no encoding word. -/
@[expose] def enc : IncomparableEncoding Unit (Bool × Option Bool) Unit Unit 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ msg _ _ := if accepts msg.2 then some ⟨word, by simp⟩ else none

/-- The accepted-output bridge needs no injectivity at rejected outputs. -/
@[expose] def bridge :
    AcceptedBridge Unit (Bool × Option Bool) Unit Unit Unit (Option Bool) 1 2 where
  enc := enc
  th := th
  epochToTweak := id
  epochToTweak_injective := Function.injective_id
  accepts := accepts
  word _ := word
  word_injOn := by
    intro x hx y hy _
    have hx' : x = some false := by simpa [accepts] using hx
    have hy' : y = some false := by simpa [accepts] using hy
    exact hx'.trans hy'.symm
  value_eq pp msg r ep := by
    simp [enc, IncomparableEncoding.value, th]
    rfl

/-- Global word injectivity fails, so this bridge is outside the historical interface. -/
theorem not_globally_injective : ¬ Function.Injective bridge.word := by
  intro h
  have hbad : (none : Option Bool) = some false := h rfl
  contradiction

/-- One successful actual target. -/
@[expose] def successfulRecord : Record (Bool × Option Bool) Unit Unit 1 2 :=
  ⟨(), (false, some false), some (word, ())⟩

/-- The shared accepted-output invariant contains the exact successful encoding equation. -/
theorem successful_record_wellFormed : WellFormed bridge.toTransport () [successfulRecord] := by
  intro entry hentry target r hresult
  have heq : entry = successfulRecord := by simpa using hentry
  subst entry
  have hpair : word = target ∧ () = r := by simpa [successfulRecord] using hresult
  obtain ⟨rfl, rfl⟩ := hpair
  rfl

/-- Same accepted hash output with a fresh message tag is transported to the actual hash game. -/
theorem accepted_collision_transports :
    SM_DT_RTCR_IsCollision (hashProblem bridge.toTransport 1 1) ()
      (targetHistory bridge.toTransport [successfulRecord])
      (witnessIndex bridge.toTransport () [successfulRecord] ((true, some false), (), ()),
        (true, some false), ()) = true :=
  valid_implies_hash_collision bridge.toTransport 1 1 () [successfulRecord]
    ((true, some false), (), ()) successful_record_wellFormed (by decide)

/-- A rejected target fabricated with the same word as an accepted output. -/
@[expose] def fabricatedRecord : Record (Bool × Option Bool) Unit Unit 1 2 :=
  ⟨(), (false, none), some (word, ())⟩

/-- Word equality alone holds for the fabricated record. -/
theorem fabricated_word_equality :
    word = bridge.word
      (bridge.th.eval () (bridge.epochToTweak ()) (fabricatedRecord.message, ())) :=
  rfl

/-- The fabricated record fails the actual-success invariant. -/
theorem fabricated_not_wellFormed : ¬ WellFormed bridge.toTransport () [fabricatedRecord] := by
  intro h
  have hvalue := AcceptedBridge.value_eq_some_of_wellFormed bridge () [fabricatedRecord]
    h fabricatedRecord (by simp) word () rfl
  contradiction

/-- A word-only transcript can pass the source collision test despite containing a rejected
target. -/
theorem fabricated_source_win :
    valid enc () [fabricatedRecord] ((true, some false), (), ()) = true := by decide

/-- The fabricated target is not a hash collision, which pins the need for actual acceptance. -/
theorem fabricated_hash_loses :
    SM_DT_RTCR_IsCollision (hashProblem bridge.toTransport 1 1) ()
      (targetHistory bridge.toTransport [fabricatedRecord])
      (0, (true, some false), ()) = false := by
  decide

example := @AcceptedBridge.advantage_le_hash
example := @TargetCollisionReduction.advantage_le_hash
example := @TargetCollisionReduction.WellFormed

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``AcceptedBridge.accepted_of_value_eq_some,
    ``AcceptedBridge.value_eq_some_of_wellFormed,
    ``AcceptedBridge.advantage_le_hash,
    ``TargetCollisionTransport.sourceCoupled_run_preserves_inv,
    ``TargetCollisionTransport.source_experiment_eq_coupled,
    ``TargetCollisionTransport.target_experiment_eq_coupled,
    ``TargetCollisionReduction.valid_implies_hash_collision,
    ``TargetCollisionReduction.sourceCoupledChallenge_preserves_inv,
    ``TargetCollisionReduction.advantage_le_hash,
    ``not_globally_injective,
    ``accepted_collision_transports,
    ``fabricated_not_wellFormed,
    ``fabricated_hash_loses]

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Reductions.EncodingAcceptedOutput,
      `HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction]
    #[(``AcceptedBridge.advantage_le_hash,
        `HashSig.GXMSS.Security.Reductions.EncodingAcceptedOutput),
      (``TargetCollisionReduction.advantage_le_hash,
        `HashSig.GXMSS.Security.Reductions.EncodingTargetCollisionReduction)]
    #[]

end GXMSS.Encoding.AcceptedBridgeProbe
