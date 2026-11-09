/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Completeness
public import VCVio.CryptoFoundations.PRF
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.EvalDist.Monad.Measure

/-!
# Shared-key hypertree derivation layouts

The request domain describes actual full-response calls. Individual starts and independent
attempts use separate calls in the IID layout. Paired starts share one full response and
counter retries use one base request per coordinate/message. A single PRF key covers the whole
forest; its ideal interpreter has one persistent cache of full responses.
-/

public section

namespace GXMSS.Hypertree.PRFDerived

open Encoding OracleComp OracleSpec

/-- Actual full-response request layouts. -/
inductive Layout where
  /-- One response per start and one response per retry attempt. -/
  | iid
  /-- Two starts per response and one base response for each bounded counter traversal. -/
  | pairedCounter
  deriving DecidableEq

/-- A start request identifies one individual start or one group of two starts. -/
@[expose, reducible] def StartIndex (S : Shape) : Layout → Type
  | .iid => Fin S.v
  | .pairedCounter => Fin ((S.v + 1) / 2)

/-- An IID request carries its bounded attempt; a counter plan has only one base request. -/
@[expose, reducible] def RetryIndex : Layout → ℕ → Type
  | .iid, budget => Fin budget
  | .pairedCounter, _ => Unit

/-- The actual shared full-response query domain, including full message fibres. -/
inductive Query (PP M H : Type) (S : Shape) (layout : Layout)
    (budget : OTSPosition S → ℕ) where
  /-- Distinguished common public-parameter response. -/
  | publicSeed
  /-- One individual or grouped start response. -/
  | start (pp : PP) (position : OTSPosition S) (index : StartIndex S layout)
  /-- A bounded IID attempt or the single counter base at this full coordinate/message. -/
  | retry (pp : PP) (position : OTSPosition S) (message : Message S M H position)
      (index : RetryIndex layout (budget position))

/-- Interpret complete responses without identifying distinct request coordinates. -/
structure Interpretation (PP H R Response : Type) where
  /-- Public parameter derived from its distinguished response. -/
  publicParameter : Response → PP
  /-- The start projection used by individual-start requests. -/
  chainStart : Response → H
  /-- Both jointly interpreted halves of a grouped response. -/
  chainPair : Response → H × H
  /-- One randomizer, or the base of a bounded counter traversal. -/
  retryRandomizer : Response → R

variable {PP T X M H R Response Key : Type} {S : Shape}

/-- The group containing a chain start; legal indices never wrap into another group. -/
@[expose] def startGroup (S : Shape) (i : Fin S.v) : Fin ((S.v + 1) / 2) :=
  ⟨i.val / 2, by have := i.isLt; omega⟩

/-- Which half of the complete grouped response supplies a chain start. -/
@[expose] def startHalf (i : Fin S.v) : Fin 2 := ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩

/-- The full group/half pair recovers the original chain coordinate exactly. -/
theorem startGroup_recompose (S : Shape) (i : Fin S.v) :
    (startGroup S i).val * 2 + (startHalf i).val = i.val := by
  simpa only [startGroup, startHalf, Nat.mul_comm] using Nat.div_add_mod i.val 2

/-- Grouping retains distinct chain coordinates jointly with their half selectors. -/
theorem startGroup_half_injective (S : Shape) :
    Function.Injective (fun i : Fin S.v => (startGroup S i, startHalf i)) := by
  intro i j h
  have hg := congrArg (fun p : Fin ((S.v + 1) / 2) × Fin 2 => p.1.val * 2 + p.2.val) h
  apply Fin.ext
  simpa only [startGroup_recompose] using hg

/-- One public-parameter request is shared by every layer and tree. -/
@[expose] def publicSeed {layout : Layout} {budget : OTSPosition S → ℕ}
    (evaluate : Key → Query PP M H S layout budget → Response)
    (interpretation : Interpretation PP H R Response) (key : Key) : PP :=
  interpretation.publicParameter (evaluate key .publicSeed)

/-- Start interpretation uses the layout's actual full-response request labels. -/
@[expose] def starts (layout : Layout) (budget : OTSPosition S → ℕ)
    (evaluate : Key → Query PP M H S layout budget → Response)
    (interpretation : Interpretation PP H R Response) (key : Key) (pp : PP) :
    OTSPosition S → Fin S.v → H :=
  match layout with
  | .iid => fun p i => interpretation.chainStart (evaluate key (.start pp p i))
  | .pairedCounter => fun p i =>
      let pair := interpretation.chainPair (evaluate key (.start pp p (startGroup S i)))
      if (startHalf i).val = 0 then pair.1 else pair.2

/-- Retry-coin interpretation is local to the actual bounded response family.
It does not assume a whole signing-game or security-game equivalence. -/
structure RetryInterpretation (layout : Layout) (sampling : RetrySampling R)
    (Response : Type) where
  /-- Decode the bottom plan's finite coins from its actual response calls. -/
  bottomCoins : (RetryIndex layout sampling.bottom.budget → Response) → sampling.bottom.Coins
  /-- Decode the internal plan's finite coins from its actual response calls. -/
  internalCoins :
    (RetryIndex layout sampling.internal.budget → Response) → sampling.internal.Coins

/-- Budget associated with a coordinate's message kind. -/
@[expose] def retryBudget (sampling : RetrySampling R) (p : OTSPosition S) : ℕ :=
  if p.1.1.val = 0 then sampling.bottom.budget else sampling.internal.budget

/-- Convert a bottom attempt label to its full-coordinate budget index. -/
@[expose] def bottomRetryIndex (layout : Layout) (sampling : RetrySampling R)
    (ep : Epoch S) (i : RetryIndex layout sampling.bottom.budget) :
    RetryIndex layout (retryBudget sampling (bottomPosition S ep)) := by
  simpa [retryBudget, bottomPosition] using i

/-- Convert an internal attempt/base label to its full-coordinate budget index. -/
@[expose] def internalRetryIndex (layout : Layout) (sampling : RetrySampling R)
    (p : UpperPosition S) (i : RetryIndex layout sampling.internal.budget) :
    RetryIndex layout (retryBudget sampling p.val) := by
  simpa [retryBudget, p.property] using i

/-- Derive every fixed internal tape from one evaluator key and its fixed child-root message.
The complete response domain remains layout-indexed; no individual labels alias grouped calls. -/
@[expose] def coreSecretKey (hash : HashInstance PP T X H S) (layout : Layout)
    (sampling : RetrySampling R)
    (evaluate : Key → Query PP M H S layout (retryBudget sampling) → Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) (key : Key) :
    Hypertree.SecretKey PP H sampling.internal.Coins S :=
  let pp := publicSeed evaluate interpretation key
  let startTable := starts layout (retryBudget sampling) evaluate interpretation key pp
  let ends := Hypertree.endpoints hash pp startTable
  ⟨pp, startTable, ends, fun p => retry.internalCoins fun i => evaluate key
    (.retry pp p.val (internalMessage p (componentRoot hash pp ends (childTree S p)))
      (internalRetryIndex layout sampling p i))⟩

/-- Derive the top public root and retain exactly the original evaluator key as secret key. -/
@[expose] def keys (hash : HashInstance PP T X H S) (layout : Layout)
    (sampling : RetrySampling R)
    (evaluate : Key → Query PP M H S layout (retryBudget sampling) → Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) (key : Key) :
    GXMSS.PublicKey PP H × Key :=
  let sk := coreSecretKey hash layout sampling evaluate interpretation retry key
  (⟨componentRoot hash sk.seed sk.endpoints (topTree S), sk.seed⟩, key)

/-- The secret key is the exact key supplied to the composite evaluator. -/
@[simp] theorem keys_snd (hash : HashInstance PP T X H S) (layout : Layout)
    (sampling : RetrySampling R)
    (evaluate : Key → Query PP M H S layout (retryBudget sampling) → Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) (key : Key) :
    (keys hash layout sampling evaluate interpretation retry key).2 = key := rfl

/-- One fresh-message retry tape is derived at the bottom coordinate with its exact message. -/
@[expose] def bottomCoins (layout : Layout) (sampling : RetrySampling R)
    (evaluate : Key → Query PP M H S layout (retryBudget sampling) → Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (key : Key) (ep : Epoch S) (msg : M) : sampling.bottom.Coins :=
  let pp := publicSeed evaluate interpretation key
  retry.bottomCoins fun i => evaluate key
    (.retry pp (bottomPosition S ep) (bottomMessage ep msg)
      (bottomRetryIndex layout sampling ep i))

/-- Deterministic signing uses the direct explicit-input algorithm with the same persistent
internal tapes for every request through the same fixed child root. -/
@[expose] def sign (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (evaluate : Key → Query PP M H S layout (retryBudget sampling) → Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (key : Key) (ep : Epoch S) (msg : M) : ProbComp (Option (Hypertree.Signature R H S)) :=
  pure (signWithCoins hash family sampling
    (coreSecretKey hash layout sampling evaluate interpretation retry key) ep msg
    (bottomCoins layout sampling evaluate interpretation retry key ep msg))

/-- Parameterless derived key generation samples one key for the whole forest. -/
@[expose] def keygen (hash : HashInstance PP T X H S) (layout : Layout)
    (sampling : RetrySampling R)
    (prf : PRFScheme Key (Query PP M H S layout (retryBudget sampling)) Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) :
    ProbComp (GXMSS.PublicKey PP H × Key) :=
  keys hash layout sampling prf.eval interpretation retry <$> prf.keygen

/-- A shared-key derived forest with deterministic signing and the direct all-input verifier. -/
@[expose] def scheme [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (prf : PRFScheme Key (Query PP M H S layout (retryBudget sampling)) Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) :
    SyncSignatureAlg ProbComp M (GXMSS.PublicKey PP H) Key
      (Hypertree.Signature R H S) (Epoch S) where
  keygen := keygen hash layout sampling prf interpretation retry
  sign := sign hash family layout sampling prf.eval interpretation retry
  verify := Hypertree.verify hash family

/-- IID coin decoding reads one actual response at each bounded attempt coordinate. -/
@[expose] noncomputable def RetryInterpretation.iid [SampleableType R]
    (bottomBudget internalBudget : ℕ) (interpretation : Interpretation PP H R Response) :
    RetryInterpretation .iid (RetrySampling.iid (R := R) bottomBudget internalBudget) Response where
  bottomCoins responses i := interpretation.retryRandomizer (responses i)
  internalCoins responses i := interpretation.retryRandomizer (responses i)

/-- Counter coin decoding reads the complete response at the single base-request coordinate. -/
@[expose] noncomputable def RetryInterpretation.counter (modulus bottomBudget internalBudget : ℕ)
    (hbottom : bottomBudget ≤ modulus) (hinternal : internalBudget ≤ modulus)
    [SampleableType (Fin modulus)]
    (interpretation : Interpretation PP H (Fin modulus) Response) :
    RetryInterpretation .pairedCounter
      (RetrySampling.counter modulus bottomBudget internalBudget hbottom hinternal) Response where
  bottomCoins responses := interpretation.retryRandomizer (responses ())
  internalCoins responses := interpretation.retryRandomizer (responses ())

/-- Explicit derived keys have the same endpoint and top-root consistency as direct keys. -/
theorem consistent_keys (hash : HashInstance PP T X H S) (layout : Layout)
    (sampling : RetrySampling R)
    (evaluate : Key → Query PP M H S layout (retryBudget sampling) → Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) (key : Key) :
    Hypertree.Consistent hash (keys hash layout sampling evaluate interpretation retry key).1
      (coreSecretKey hash layout sampling evaluate interpretation retry key) := by
  simp [Hypertree.Consistent, keys, coreSecretKey]

/-- Every successful derived signature verifies under its derived public key. -/
theorem verify_of_mem_support_sign [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (evaluate : Key → Query PP M H S layout (retryBudget sampling) → Response)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (key : Key) (ep : Epoch S) (msg : M) (sig : Hypertree.Signature R H S)
    (hsig : some sig ∈ support (sign hash family layout sampling evaluate interpretation retry
      key ep msg)) :
    Hypertree.verify hash family (keys hash layout sampling evaluate interpretation retry key).1
      ep msg sig = true := by
  have hs : signWithCoins hash family sampling
      (coreSecretKey hash layout sampling evaluate interpretation retry key) ep msg
      (bottomCoins layout sampling evaluate interpretation retry key ep msg) = some sig := by
    symm
    simpa [sign] using hsig
  exact Hypertree.verify_signWithCoins hash family sampling _ _
    (consistent_keys hash layout sampling evaluate interpretation retry key) ep msg _ sig hs

/-- The ideal interpreter stores the complete response at each actual request coordinate. -/
noncomputable def cachedQueryImpl {layout : Layout} {budget : OTSPosition S → ℕ}
    [DecidableEq (Query PP M H S layout budget)] [SampleableType Response] :
    QueryImpl (PRFScheme.PRFOracleSpec (Query PP M H S layout budget) Response)
      (StateT ((Query PP M H S layout budget →ₒ Response).QueryCache) ProbComp) :=
  PRFScheme.prfIdealQueryImpl

/-- A cached request returns the same complete response, without discarding either half. -/
theorem cachedQuery_replay {layout : Layout} {budget : OTSPosition S → ℕ}
    [DecidableEq (Query PP M H S layout budget)] [SampleableType Response]
    (cache : (Query PP M H S layout budget →ₒ Response).QueryCache)
    (q : Query PP M H S layout budget) (response : Response) (h : cache q = some response) :
    ((cachedQueryImpl (Sum.inr q)).run cache) = pure (response, cache) := by
  change (((Query PP M H S layout budget →ₒ Response).randomOracle q).run cache) = _
  exact QueryImpl.withCaching_run_some _ h

/-- A bijective full-response decoder supplies the joint pair law.
Separate uniform marginal laws would not establish this equation. -/
theorem jointPairSampling [SampleableType Response] [SampleableType H]
    (decode : Response ≃ H × H) :
    decode <$> ($ᵗ Response : ProbComp Response) =ᵈ
      (do let left ← ($ᵗ H : ProbComp H); let right ← ($ᵗ H); pure (left, right)) := by
  apply EvalDistEq.of_forall_prEvent_eq
  intro event
  rw [prEvent_map, SampleableType.prEvent_uniformSample_comp_of_bijective decode.bijective,
    SampleableType.prEvent_uniformSample_prod]
  simp

end GXMSS.Hypertree.PRFDerived
