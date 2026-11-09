/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Completeness
public import HashSig.GXMSS.Hypertree.PRFDerivedScheme

/-! # Ordinary public-import hypertree consumers

The construction and correctness endpoints are applied without importing hidden implementation
bodies. Strategy-specific failure laws remain explicit.
-/

public section

namespace GXMSS.Hypertree.Test

open Encoding ENNReal

variable {PP T X H M R : Type} {S : Shape}

example [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S)
    (hc : Consistent hash pk sk) (ep : Epoch S) (msg : M) (sig : Signature R H S)
    (hs : some sig ∈ support (sign hash family sampling sk ep msg)) :
    verify hash family pk ep msg sig = true :=
  verify_of_mem_support_sign hash family sampling pk sk hc ep msg sig hs

example [SampleableType H] [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (bottomError internalError : ℝ≥0∞)
    (herror : RetryFailureBounds family sampling bottomError internalError) :
    (scheme hash family sampling).AverageComplete ProbCompRuntime.probComp
      (bottomError + (S.d - 1 : ℕ) * internalError) :=
  average_complete hash family sampling bottomError internalError herror

example {Key Response : Type} [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : PRFDerived.Layout) (sampling : RetrySampling R)
    (eval : Key → PRFDerived.Query PP M H S layout (PRFDerived.retryBudget sampling) → Response)
    (interpretation : PRFDerived.Interpretation PP H R Response)
    (retry : PRFDerived.RetryInterpretation layout sampling Response)
    (key : Key) (ep : Epoch S) (msg : M) (sig : Signature R H S)
    (hs : some sig ∈ support (PRFDerived.sign hash family layout sampling eval interpretation
      retry key ep msg)) :
    verify hash family (PRFDerived.keys hash layout sampling eval interpretation retry key).1
      ep msg sig = true :=
  PRFDerived.verify_of_mem_support_sign hash family layout sampling eval interpretation retry
    key ep msg sig hs

end GXMSS.Hypertree.Test
