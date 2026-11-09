/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Unforgeability
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedQueryBounds
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling
import all HashSig.GXMSS.Security.Hypertree.Reductions.PRFDerivedOracleInteraction
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Hypertree.PRFDerivedScheme
import all VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.PRF

/-!
# Shared-PRF arbitrary-depth hypertree security

One full-response cache spans setup and every adaptive signing request. The local sampling laws
are layout-indexed: IID retry tapes and grouped counter bases use different domains and laws.
The encoding advantage remains the exact strategy-dependent mixed-fibre game.
-/

public section

namespace GXMSS.Hypertree.PRFDerived.Unforgeability
open OracleComp OracleSpec ENNReal MeasureTheory

variable {PP T X H M R Y Response Key : Type} {S : Shape}

/-- The ideal shared-cache experiment is the direct construction's strong winning measure. -/
theorem randgenPRFReduction_ideal_strong [SampleableType H] [SampleableType Response]
    [DecidableEq H] [DecidableEq M] [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)] (adv : SchemeAdversary PP H M R S) :
    𝒟[PRFScheme.prfIdealExperiment
      (randgenPRFReduction hash family layout sampling interpretation retry adv)] =
        SyncSignatureUnforgeability.strongUnforgeableExp
          (Hypertree.scheme hash family sampling) ProbCompRuntime.probComp adv := by
  have hwin : SyncSignatureUnforgeability.strongValid
      (oracleScheme hash family layout sampling interpretation retry) =
      SyncSignatureUnforgeability.strongValid (Hypertree.scheme hash family sampling) := by
    funext out
    rfl
  have h := (oracleInteraction_ideal_eq_interaction hash family layout sampling interpretation
    retry laws adv).map (SyncSignatureUnforgeability.strongValid
      (oracleScheme hash family layout sampling interpretation retry))
  rw [hwin] at h
  simpa only [PRFScheme.prfIdealExperiment, randgenPRFReduction, simulateQ_map, hwin,
    GXMSS.PRFDerived.ResponseCache.state_run'_map,
    SyncSignatureUnforgeability.strongUnforgeableExp,
    SyncSignatureUnforgeability.outputMeasure, ProbCompRuntime.probComp_evalDist]
    using h.evalDist_eq

/-- One additive PRF advantage transports the complete strong source game. -/
theorem adaptive_strong_additive_bound [SampleableType H] [SampleableType Response]
    [DecidableEq H] [DecidableEq M] [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (adv : SchemeAdversary PP H M R S) :
    SyncSignatureUnforgeability.strongAdvantage
      (PRFDerived.scheme hash family layout sampling prf interpretation retry)
      ProbCompRuntime.probComp adv ≤
        prf.prfAdvantage
          (randgenPRFReduction hash family layout sampling interpretation retry adv) +
          SyncSignatureUnforgeability.strongAdvantage (Hypertree.scheme hash family sampling)
            ProbCompRuntime.probComp adv := by
  have hreal : 𝒟[prf.prfRealExperiment
        (randgenPRFReduction hash family layout sampling interpretation retry adv)] =
      SyncSignatureUnforgeability.strongUnforgeableExp
        (PRFDerived.scheme hash family layout sampling prf interpretation retry)
        ProbCompRuntime.probComp adv := by
    rw [randgenPRFReduction_real_strong]
    rfl
  have hideal := randgenPRFReduction_ideal_strong hash family layout sampling interpretation
    retry laws adv
  unfold PRFScheme.prfAdvantage
  rw [hreal, hideal]
  rw [add_comm]
  exact Measure.apply_true_le_add_boolDist _ _

/-- One PRF advantage plus the explicit six-term global direct bound. -/
@[expose] noncomputable def strongUnforgeabilityBound [SampleableType H]
    [SampleableType Response] [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq M] [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w) (adv : SchemeAdversary PP H M R S) : ℝ≥0∞ :=
  prf.prfAdvantage (randgenPRFReduction hash family layout sampling interpretation retry adv) +
    Hypertree.Unforgeability.strongUnforgeabilityBound hash family sampling qs hv hw adv

/-- The shared-key derived scheme has one additive PRF term and the sharp direct forest bound. -/
theorem strong_unforgeability_reduction_bound [SampleableType H] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w) (hnonmax : family.NoMaximumOutput)
    (adv : SchemeAdversary PP H M R S)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    SyncSignatureUnforgeability.strongAdvantage
      (PRFDerived.scheme hash family layout sampling prf interpretation retry)
      ProbCompRuntime.probComp adv ≤
        strongUnforgeabilityBound hash family layout sampling interpretation retry
          prf qs hv hw adv :=
  (adaptive_strong_additive_bound hash family layout sampling interpretation retry
    laws prf adv).trans
    (add_le_add (le_refl _) (Hypertree.Unforgeability.strong_unforgeability_reduction_bound
      hash family sampling qs hv hw hnonmax adv hqueries))

/-- The ordinary game is bounded by the same concrete global reductions and shared PRF term. -/
theorem unforgeability_reduction_bound [SampleableType H] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w) (hnonmax : family.NoMaximumOutput)
    (adv : SchemeAdversary PP H M R S)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    SyncSignatureUnforgeability.advantage
      (PRFDerived.scheme hash family layout sampling prf interpretation retry)
      ProbCompRuntime.probComp adv ≤
        strongUnforgeabilityBound hash family layout sampling interpretation retry
          prf qs hv hw adv :=
  (SyncSignatureUnforgeability.advantage_le_strongAdvantage _ _ _).trans
    (strong_unforgeability_reduction_bound hash family layout sampling interpretation retry laws
      prf qs hv hw hnonmax adv hqueries)

/-- One actual PRF advantage plus the native accepted-hash global bound with the captured
mixed retry strategies. Correlated counter trials retain their own hash primitive. -/
@[expose] noncomputable def hashEncodingStrongUnforgeabilityBound [SampleableType H]
    [SampleableType Response] [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq M] [DecidableEq R] [DecidableEq Y]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w)
    (encodingHash : Security.FamilyEncodingAcceptedOutput.HashFamily PP M H R Y S)
    (hinjective : ∀ p, Set.InjOn (encodingHash.word p)
      {y | encodingHash.accepts p y = true})
    (hvalue : ∀ pp q r, family.value q.1 pp q.2 r =
      if encodingHash.accepts q.1 (encodingHash.eval pp q r) then
        some (encodingHash.word q.1 (encodingHash.eval pp q r)) else none)
    (adv : SchemeAdversary PP H M R S) : ℝ≥0∞ :=
  prf.prfAdvantage (randgenPRFReduction hash family layout sampling interpretation retry adv) +
    Hypertree.Unforgeability.hashEncodingStrongUnforgeabilityBound hash family sampling qs hv hw
      encodingHash hinjective hvalue adv

/-- The real derived scheme has one PRF term and six native hash terms under the exact local
sampling laws and accepted-output bridge. No law about a uniformly distributed derived key is
required: the real game uses the supplied PRF's actual key generator. -/
theorem strong_unforgeability_reduction_bound_hashEncoding [SampleableType H]
    [SampleableType Response] [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq M] [DecidableEq R] [DecidableEq Y]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w) (hnonmax : family.NoMaximumOutput)
    (encodingHash : Security.FamilyEncodingAcceptedOutput.HashFamily PP M H R Y S)
    (hinjective : ∀ p, Set.InjOn (encodingHash.word p)
      {y | encodingHash.accepts p y = true})
    (hvalue : ∀ pp q r, family.value q.1 pp q.2 r =
      if encodingHash.accepts q.1 (encodingHash.eval pp q r) then
        some (encodingHash.word q.1 (encodingHash.eval pp q r)) else none)
    (adv : SchemeAdversary PP H M R S)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    SyncSignatureUnforgeability.strongAdvantage
      (PRFDerived.scheme hash family layout sampling prf interpretation retry)
      ProbCompRuntime.probComp adv ≤
        hashEncodingStrongUnforgeabilityBound hash family layout sampling interpretation retry
          prf qs hv hw encodingHash hinjective hvalue adv :=
  (adaptive_strong_additive_bound hash family layout sampling interpretation retry
    laws prf adv).trans
    (add_le_add (le_refl _)
      (Hypertree.Unforgeability.strong_unforgeability_reduction_bound_hashEncoding
        hash family sampling qs hv hw hnonmax encodingHash hinjective hvalue adv hqueries))

end GXMSS.Hypertree.PRFDerived.Unforgeability
