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
