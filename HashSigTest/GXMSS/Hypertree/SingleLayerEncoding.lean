/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Depth-one actual encoding-game controls

The game transport retains exhausted records and exact message/randomizer freshness. The consumer
uses the actual ordinary experiment with its explicit translated adaptive strategy.
-/

public section

namespace GXMSS.Hypertree.SingleLayer.EncodingTransport.Probe

open Encoding OracleComp OracleSpec
open GXMSS.Hypertree.Security

/-- One legal epoch, with a one-digit code. -/
@[expose, reducible] def shape := singleShape 0 1 1

/-- The only codeword used by the fixture. -/
@[expose] def word : Codeword 1 2 := fun _ => 0

/-- The encoding admits different messages at the same selected word. -/
@[expose] def encoding : IncomparableEncoding Unit Bool Bool (Fin 1) 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r then some ⟨word, Set.mem_singleton _⟩ else none

/-- The full-coordinate query retains its first application message. -/
@[expose] def query : FamilyEncoding.Query Bool Unit shape :=
  ⟨bottomPosition shape 0, bottomMessage 0 true⟩

/-- A failed query is still a consumed target record. -/
theorem failed_record_consumed :
    TargetCollisionResistance.used
      (transcriptObservation [⟨query.1, query.2, (none : Option (Codeword 1 2 × Bool))⟩]) 0 =
        true := by decide

/-- A failed record remains unavailable for a later message. -/
theorem failed_record_duplicate_rejected :
    TargetCollisionResistance.rejected 2
      (transcriptObservation [⟨query.1, query.2, (none : Option (Codeword 1 2 × Bool))⟩]) 0 =
        true := by decide

/-- Exact application-message/randomizer replay stays invalid after coordinate observation. -/
theorem exact_pair_rejected :
    TargetCollisionResistance.valid encoding ()
      (transcriptObservation [⟨query.1, query.2, some (word, true)⟩])
      (candidateObservation ⟨query, true⟩) = false := by decide

/-- A distinct application message can witness the same selected word. -/
theorem distinct_message_retained :
    TargetCollisionResistance.valid encoding ()
      (transcriptObservation [⟨query.1, query.2, some (word, true)⟩])
      (candidateObservation (H := Unit) ⟨⟨query.1, bottomMessage 0 false⟩, true⟩) = true := by
  decide

example {PP T X H M R : Type} {h w v : ℕ} [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : FamilyEncoding.Adversary (problem (H := H) hash enc qs K J)) :
    FamilyEncoding.experiment adv =ᵈ
      TargetCollisionResistance.experiment (adversaryToOrdinary hash enc qs K J adv) :=
  experiment_evalDistEq hash enc qs K J adv

/-- A failed signing request remains occupied in the complete observed private state. -/
theorem failed_history_occupied :
    (stateObservation (H := Unit) (h := 0) (w := 1) (v := 1)
      ((fun _ => some (true, none)),
        [⟨query.1, query.2, (none : Option (Codeword 1 2 × Bool))⟩])).1 0 =
          some (true, none) := by
  rfl

/-- Ordinary public imports expose the actual historical named experiment correspondence. -/
example {PP T X H M R : Type} {h w v : ℕ} [SampleableType H] [SampleableType R]
    [DecidableEq M] [DecidableEq H] [DecidableEq R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (qs K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    FamilyEncoding.experiment (Security.encodingTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) qs adv) =ᵈ
      TargetCollisionResistance.experiment (GXMSS.Reductions.encodingTargetCollisionReduction
        hash enc qs K (SingleLayer.adversaryToOrdinary adv)) :=
  historical_reduction_experiment_evalDistEq hash enc qs K J adv hqueries

example := @SingleLayer.sourceProgram_iid_evalDistEq
example := @SingleLayer.strongUnforgeableExp_iid_eq
example := @SingleLayer.unforgeableExp_iid_eq
example := @SingleLayer.sourceProgram_history_has_attempt
example := @reduction_advantage_eq
example := @historical_reduction_advantage_eq
example := @adversaryToOrdinary_queryBound

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding]
    #[(``experiment_evalDistEq,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding),
      (``historical_reduction_experiment_evalDistEq,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding),
      (``historical_reduction_advantage_eq,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding),
      (``candidateObservation_select,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding),
      (``signFromResults_single,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding),
      (``advantage_eq, `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding),
      (``SingleLayer.sourceProgram_iid_evalDistEq,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource),
      (``SingleLayer.strongUnforgeableExp_iid_eq,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource),
      (``SingleLayer.unforgeableExp_iid_eq,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource),
      (``SingleLayer.sourceProgram_history_has_attempt,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource)]
    #[]
    #[(``adversaryToOrdinary, `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding)]

end GXMSS.Hypertree.SingleLayer.EncodingTransport.Probe
