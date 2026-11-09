/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Reductions.ChainCutCollision
public import HashSig.GXMSS.Security.Hypertree.Reductions.EncodingCollision
public import HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage

/-!
# Arbitrary-depth hypertree unforgeability

The native synchronized source experiment is bounded by four collision games and two
original-domain chain games. One selector ranges over all positive chain positions in the
forest. Retry exhaustion, consumed failed requests, private fixed certificates and strong
message/signature-pair freshness remain in the source computation.

The explicit fibrewise `NoMaximumOutput` hypothesis supplies a positive selected step for an
unused or exhausted reference. It is an additional nondegeneracy condition on the arbitrary
incomparable encoding family; shape positivity alone does not imply it.
-/

public section

namespace GXMSS.Hypertree.Unforgeability

open ENNReal OracleComp OracleSpec TweakableHash

variable {PP T X H M R : Type} {S : Shape}

/-- The six named global reductions with the exact forest and positive-step coefficients. -/
@[expose] noncomputable def strongUnforgeabilityBound [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : Security.SchemeAdversary PP H M R S) : ℝ≥0∞ :=
  SM_DT_TCR_Advantage (merkleTargetCollisionReduction hash family sampling adv) +
    Security.FamilyEncoding.advantage
      (Security.encodingTargetCollisionReduction hash family sampling qs adv) +
    SM_DT_TCR_Advantage (sameMessageChainTargetCollisionReduction hash family sampling adv) +
    SM_DT_TCR_Advantage (chainCutTargetCollisionReduction hash family sampling adv) +
    (chainCount S : ℝ≥0∞) *
      SM_DT_PRE_Advantage (Security.chainPreimageReduction hash family sampling hv hw adv) +
    (chainCount S : ℝ≥0∞) * ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) *
      SM_DT_UD_Advantage (Security.chainUndetectabilityReduction hash family sampling hv hw adv
        (Security.selectedCutObservation hash family))

/-- Four actual collision reductions and one global PRE/UD pair bound every strong forgery.
The signing-query bound governs the family encoding game. No reduction running-time or
reduction-query complexity bound is asserted here. -/
theorem strong_unforgeability_reduction_bound [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w)
    (hnonmax : family.NoMaximumOutput) (adv : Security.SchemeAdversary PP H M R S)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    SyncSignatureUnforgeability.strongAdvantage (scheme hash family sampling)
      ProbCompRuntime.probComp adv ≤
      strongUnforgeabilityBound hash family sampling qs hv hw adv := by
  let : NeZero (2 ^ S.w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (Nat.ne_of_gt hw); omega⟩
  let : MeasurableSpace (Security.Result PP H M R sampling.internal.Coins S) := ⊤
  have hresidual : 𝒟[sourceResidual hash family sampling <$>
        Security.sourceProgram hash family sampling adv] {true} ≤
      (chainCount S : ℝ≥0∞) *
          SM_DT_PRE_Advantage (Security.chainPreimageReduction hash family sampling hv hw adv) +
        (chainCount S : ℝ≥0∞) * ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (Security.chainUndetectabilityReduction hash family sampling hv hw adv
            (Security.selectedCutObservation hash family)) := by
    rw [evalDist_map_apply _ Measurable.of_discrete (measurableSet_singleton true)]
    exact Security.sourceResidual_mass_le_chain hash family sampling hv hw adv hnonmax
  have hpart := sourceStrong_mass_le_partition hash family sampling adv
  have hfour := add_le_add
    (add_le_add
      (add_le_add (sourceMerkleBad_le_targetCollision hash family sampling adv hv)
        (Security.sourceEncodingBad_mass_le_familyAdvantage hash family sampling qs adv hqueries))
      (sourceSameWordBad_le_targetCollision hash family sampling adv))
    (sourceChainCutBad_le_targetCollision hash family sampling adv)
  have h := hpart.trans (add_le_add hfour hresidual)
  rw [Security.sourceStrongOutputMeasure_eq_strongUnforgeableExp] at h
  simpa only [SyncSignatureUnforgeability.strongAdvantage, strongUnforgeabilityBound,
    add_assoc] using h

/-- Ordinary unforgeability follows for the same six concrete reductions and native runtime. -/
theorem unforgeability_reduction_bound [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w)
    (hnonmax : family.NoMaximumOutput) (adv : Security.SchemeAdversary PP H M R S)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    SyncSignatureUnforgeability.advantage (scheme hash family sampling)
      ProbCompRuntime.probComp adv ≤
      strongUnforgeabilityBound hash family sampling qs hv hw adv := by
  classical
  exact (SyncSignatureUnforgeability.advantage_le_strongAdvantage (scheme hash family sampling)
    ProbCompRuntime.probComp adv).trans
    (strong_unforgeability_reduction_bound hash family sampling qs hv hw hnonmax adv hqueries)

end GXMSS.Hypertree.Unforgeability
