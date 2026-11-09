/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Reductions.MerkleCollision
import all HashSig.GXMSS.Hypertree.Scheme

/-!
# Global same-word chain collision reduction

All positive chain targets are registered before seed revelation. The subsequent source
interaction uses one full forest and fixed upper tapes. Same-word altered chain material at
either a bottom request or a private internal certificate selects its collision after forgery.
-/

public section

namespace GXMSS.Hypertree.Unforgeability

open OracleComp OracleSpec TweakableHash GXMSS.Security

variable {PP T X H M R : Type} {S : Shape}

/-- One global chain-target reduction, with no challenge oracle in its source/extraction phase. -/
@[expose] noncomputable def chainCollisionReduction [SampleableType H]
    [DecidableEq T] [DecidableEq X]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X)) :
    SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone hash.thf (chainCapacity S)) where
  State := ChainSetupState T X H S
  choose := chooseChains hash (chainCapacity S)
  forge state pp := do
    let coins ← sampleUpperCoins S sampling.sampleInternal
    let sk : SecretKey PP H sampling.internal.Coins S :=
      ⟨pp, state.starts, state.endpoints, coins⟩
    let pk : GXMSS.PublicKey PP H :=
      ⟨componentRoot hash pp state.endpoints (topTree S), pp⟩
    let out ← Security.runWithKeys hash family sampling adv pk sk
    pure (witnessCandidate state.targets (hash.digestInput state.fallback) (find out))

/-- The named same-word chain collision reduction includes altered same-message certificates. -/
@[expose] noncomputable def sameMessageChainTargetCollisionReduction [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S) :=
  chainCollisionReduction hash family sampling adv (sourceSameWordWitness? hash family)

/-- The chain-only target experiment retains the same complete native source interaction. -/
@[expose] noncomputable def chainCollisionProgram [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X)) :
    ProbComp Bool :=
  collisionProgram hash family sampling adv (fun pp starts _ => chainLedger hash pp starts)
    (fun fallback _ => hash.digestInput fallback) find

/-- Accepted chain-only registration gives the actual authoritative target experiment. -/
theorem chainCollisionReduction_experiment [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X)) :
    SM_DT_TCR_Experiment (chainCollisionReduction hash family sampling adv find) =
      chainCollisionProgram hash family sampling adv find := by
  unfold SM_DT_TCR_Experiment chainCollisionReduction chainCollisionProgram collisionProgram
  apply bind_congr
  intro pp
  rw [chooseChains_run hash (chainCapacity S) pp (chainCount_le_capacity S)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  apply bind_congr
  intro coins
  apply bind_congr
  intro out
  simp only [candidateCheck, SM_DT_TCR_Problem.standalone]
  split
  · simp_all only
  · simp_all only [ne_eq, PFunctor.FreeM.pure_inj]
    exact decide_eq_decide.mpr Iff.rfl

/-- A registered chain extractor bounds a native source observation in the one global game. -/
theorem chainCollisionReduction_bound [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X))
    (flag : Security.Result PP H M R sampling.internal.Coins S → Bool)
    (hfind : ∀ out, flag out = true → (find out).isSome)
    (hspec : ∀ out collision, find out = some collision →
      collision.Sound hash.thf out.sk.seed ∧
        (collision.tweak, collision.first) ∈ chainLedger hash out.sk.seed out.sk.starts) :
    𝒟[flag <$> Security.sourceProgram hash family sampling adv] {true} ≤
      SM_DT_TCR_Advantage (chainCollisionReduction hash family sampling adv find) := by
  rw [SM_DT_TCR_Advantage, chainCollisionReduction_experiment hash family sampling adv find]
  exact sourceFlag_le_collisionProgram hash family sampling adv
    (fun pp starts _ => chainLedger hash pp starts)
    (fun fallback _ => hash.digestInput fallback) find flag hfind hspec

/-- Same-word changed-chain source mass is charged once to its named global hash game. -/
theorem sourceSameWordBad_le_targetCollision [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S) :
    𝒟[sourceSameWordBad hash family sampling <$>
      Security.sourceProgram hash family sampling adv] {true} ≤
        SM_DT_TCR_Advantage
          (sameMessageChainTargetCollisionReduction hash family sampling adv) := by
  apply chainCollisionReduction_bound hash family sampling adv (sourceSameWordWitness? hash family)
    (sourceSameWordBad hash family sampling)
  · intro out h
    simp only [sourceSameWordBad, Bool.and_eq_true] at h
    exact h.2
  · exact sourceSameWordWitness?_spec hash family

end GXMSS.Hypertree.Unforgeability
