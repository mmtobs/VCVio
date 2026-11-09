/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig

/-! # Public aggregate consumers of both generic strong security endpoints -/

public section

namespace GXMSS.Hypertree.Unforgeability

variable {PP T X H M R : Type} {S : Shape}

example [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w)
    (hnonmax : family.NoMaximumOutput) (adv : Security.SchemeAdversary PP H M R S)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    SyncSignatureUnforgeability.strongAdvantage (scheme hash family sampling)
      ProbCompRuntime.probComp adv ≤
      strongUnforgeabilityBound hash family sampling qs hv hw adv :=
  strong_unforgeability_reduction_bound hash family sampling qs hv hw hnonmax adv hqueries

end GXMSS.Hypertree.Unforgeability

namespace GXMSS.Hypertree.PRFDerived.Unforgeability

variable {PP T X H M R Response Key : Type} {S : Shape}

example [SampleableType H] [SampleableType Response]
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
  strong_unforgeability_reduction_bound hash family layout sampling interpretation retry laws
    prf qs hv hw hnonmax adv hqueries

end GXMSS.Hypertree.PRFDerived.Unforgeability

namespace GXMSS.Hypertree.PRFDerived.Unforgeability

variable {PP T X H M R Y Response RawKey : Type} {S : Shape}

example [SampleableType H] [SampleableType Response]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq Y] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation .pairedCounter sampling Response)
    (laws : SamplingLaws hash .pairedCounter sampling interpretation retry)
    [DecidableEq (Domain PP M H R S .pairedCounter sampling)]
    (sourcePRF : PRFScheme RawKey (Domain PP M H R S .pairedCounter sampling) Response)
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
        (PRFDerived.scheme hash family .pairedCounter sampling sourcePRF interpretation retry)
        ProbCompRuntime.probComp adv ≤
      hashEncodingStrongUnforgeabilityBound hash family .pairedCounter sampling interpretation
        retry sourcePRF qs hv hw encodingHash hinjective hvalue adv ∧
    (randgenPRFReduction hash family .pairedCounter sampling interpretation retry adv).IsQueryBoundP
        (fun q => q.isRight = true)
          (1 + otsCount S * ((S.v + 1) / 2) + upperCount S + qs) := by
  constructor
  · exact strong_unforgeability_reduction_bound_hashEncoding hash family .pairedCounter sampling
      interpretation retry laws sourcePRF qs hv hw hnonmax encodingHash hinjective hvalue
      adv hqueries
  · simpa only [eagerQueryBound_pairedCounter] using
      randgenPRFReduction_query_bound hash family .pairedCounter sampling interpretation retry
        qs adv hqueries

end GXMSS.Hypertree.PRFDerived.Unforgeability
