/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Reductions.SameMessageChainCollision

/-!
# Global chain-cut collision reduction

The actual designated-cut finder selects a post-cut collision against one registered global
chain input. Its preimage branch remains outside this collision event and is handled separately.
-/

public section

namespace GXMSS.Hypertree.Unforgeability

open TweakableHash

variable {PP T X H M R : Type} {S : Shape}

/-- The named global designated-cut target-collision reduction. -/
@[expose] noncomputable def chainCutTargetCollisionReduction [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S) :=
  chainCollisionReduction hash family sampling adv (sourceChainCutWitness? hash family)

/-- Native cut-collision source mass is charged to the single named global chain-target game. -/
theorem sourceChainCutBad_le_targetCollision [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S) :
    𝒟[sourceChainCutBad hash family sampling <$>
      Security.sourceProgram hash family sampling adv] {true} ≤
        SM_DT_TCR_Advantage (chainCutTargetCollisionReduction hash family sampling adv) := by
  apply chainCollisionReduction_bound hash family sampling adv (sourceChainCutWitness? hash family)
    (sourceChainCutBad hash family sampling)
  · intro out h
    simp only [sourceChainCutBad, Bool.and_eq_true] at h
    exact h.2
  · exact sourceChainCutWitness?_spec hash family

end GXMSS.Hypertree.Unforgeability
