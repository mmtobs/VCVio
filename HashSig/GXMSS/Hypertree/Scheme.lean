/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.HashInstance
public import HashSig.GXMSS.Encoding.Family
public import HashSig.GXMSS.Encoding.RetryPlan
public import HashSig.GXMSS.Scheme
public import VCVio.EvalDist.IndepProduct
import all HashSig.GXMSS.Scheme

/-!
# Arbitrary-depth generalized XMSS

One public seed and hash serve all components. Internal one-time keys certify fixed child
roots using coins retained in the secret key. Retrying an internal certificate therefore
reproduces its optional result, including permanent exhaustion. The epoch remains external
to the signature; the synchronized signature interface supplies global first-request handling.
-/

public section

namespace GXMSS.Hypertree

open Encoding

/-- The bottom layer signs application messages; every other layer signs digests. -/
@[expose, reducible] def Message (S : Shape) (M H : Type) (p : OTSPosition S) : Type :=
  if p.1.1.val = 0 then M else H

/-- Separate incomparable encodings for the complete coordinates and their message fibres. -/
abbrev EncodingFamily (PP M R H : Type) (S : Shape) :=
  Encoding.Family (OTSPosition S) PP (Message S M H) R S.v (2 ^ S.w)

/-- Finite retry plans and their actual coin samplers, captured by the scheme instance.
Native `ProbComp` sampling is lossless. Encoding exhaustion is explicit; independence or
counter laws are separate sampling obligations. -/
structure RetrySampling (R : Type) where
  /-- Fresh coins for an application-message signing call. -/
  bottom : RetryPlan R
  /-- Coins fixed for each internal one-time key during key generation. -/
  internal : RetryPlan R
  /-- Actual bottom-message coin sampler. -/
  sampleBottom : ProbComp bottom.Coins
  /-- Actual internal-certificate coin sampler. -/
  sampleInternal : ProbComp internal.Coins

/-- Independent per-attempt retry coins for bottom and internal message kinds. -/
@[expose] noncomputable def RetrySampling.iid {R : Type} [SampleableType R]
    (bottomBudget internalBudget : ℕ) :
    RetrySampling R where
  bottom := RetryPlan.iid R bottomBudget
  internal := RetryPlan.iid R internalBudget
  sampleBottom := $ᵗ (Fin bottomBudget → R)
  sampleInternal := $ᵗ (Fin internalBudget → R)

/-- One uniformly sampled modular base for each bounded counter retry plan. -/
@[expose] noncomputable def RetrySampling.counter (modulus bottomBudget internalBudget : ℕ)
    (hbottom : bottomBudget ≤ modulus) (hinternal : internalBudget ≤ modulus)
    [SampleableType (Fin modulus)] : RetrySampling (Fin modulus) where
  bottom := RetryPlan.counter modulus bottomBudget hbottom
  internal := RetryPlan.counter modulus internalBudget hinternal
  sampleBottom := $ᵗ (Fin modulus)
  sampleInternal := $ᵗ (Fin modulus)

/-- A bottom component signature and all remaining bottom-to-top certificates. -/
structure Signature (R H : Type) (S : Shape) where
  /-- Signature of the application message in its bottom tree. -/
  bottom : GXMSS.Signature R H S.h S.v
  /-- Certificates in increasing layer order. -/
  upper : Fin (S.d - 1) → GXMSS.Signature R H S.h S.v

/-- Raw full-forest key material with one fixed coin value per internal one-time key. -/
structure SecretKey (PP H Coins : Type) (S : Shape) where
  /-- Common public hash parameter. -/
  seed : PP
  /-- All chain starts, indexed by full one-time-key coordinate. -/
  starts : OTSPosition S → Fin S.v → H
  /-- Stored full chain endpoints. -/
  endpoints : OTSPosition S → Fin S.v → H
  /-- Fixed retry coins, retained also when a certificate exhausts. -/
  upperCoins : UpperPosition S → Coins

variable {PP T X H M R Coins : Type} {S : Shape}

/-- Restrict raw secret material to a component without changing its data. -/
@[expose] def componentSecretKey (sk : SecretKey PP H Coins S) (p : TreePosition S) :
    GXMSS.SecretKey PP H S.h S.v :=
  ⟨sk.seed, fun ep => sk.starts (p, ep), fun ep => sk.endpoints (p, ep)⟩

/-- Full positive-step chains at every one-time-key coordinate. -/
@[expose] def endpoints (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) : OTSPosition S → Fin S.v → H :=
  fun p i => (hash.componentHash p.1).chain pp p.2 i 0 (2 ^ S.w - 1) (starts p i)

/-- A component root computed only from its endpoint table. -/
@[expose] def componentRoot (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) (p : TreePosition S) : H :=
  (hash.componentHash p).merkleRoot pp (fun ep => ends (p, ep))

/-- Assemble the public top root and raw forest secret key from explicit inputs. -/
@[expose] def keys (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (coins : UpperPosition S → Coins) :
    GXMSS.PublicKey PP H × SecretKey PP H Coins S :=
  let ends := endpoints hash pp starts
  (⟨componentRoot hash pp ends (topTree S), pp⟩, ⟨pp, starts, ends, coins⟩)

/-- Independent uniform starts for the complete forest. -/
@[expose] noncomputable def sampleStarts [SampleableType H] (S : Shape) :
    ProbComp (OTSPosition S → Fin S.v → H) := by
  letI : Fintype (OTSPosition S) := Fintype.ofFinite _
  exact Fintype.mPi fun _ => Fin.mOfFn S.v fun _ => $ᵗ H

/-- Draw each internal tape once, including tapes whose certificate will fail. -/
@[expose] noncomputable def sampleUpperCoins (S : Shape) (sample : ProbComp Coins) :
    ProbComp (UpperPosition S → Coins) := by
  letI : Fintype (UpperPosition S) := Fintype.ofFinite _
  exact Fintype.mPi fun _ => sample

/-- Parameterless key generation with the actual seed, start and fixed-tape samplers. -/
@[expose] noncomputable def keygen [SampleableType H] (hash : HashInstance PP T X H S)
    (sampling : RetrySampling R) :
    ProbComp (GXMSS.PublicKey PP H × SecretKey PP H sampling.internal.Coins S) := do
  let pp ← hash.thf.seedGen
  let starts ← sampleStarts S
  let coins ← sampleUpperCoins S sampling.sampleInternal
  pure (keys hash pp starts coins)

/-- First-success retry metadata for a fixed one-time coordinate and explicit coins. -/
@[expose] def componentResult (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H Coins S) (p : OTSPosition S) (msg : Message S M H p)
    (coins : plan.Coins) : IncomparableEncoding.IndexedResult R S.v (2 ^ S.w) :=
  plan.run (family.atEpoch p (Fin S.branching)) sk.seed msg p.2 coins

/-- Materialize one component signature from successful retry data. -/
@[expose] def componentSignature (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Coins S) (p : OTSPosition S)
    (wr : Codeword S.v (2 ^ S.w) × R) : GXMSS.Signature R H S.h S.v :=
  GXMSS.signatureOfWord (hash.componentHash p.1) (componentSecretKey sk p.1) p.2 wr

/-- Interpret an internal digest in its coordinate's message fibre. -/
@[expose] def internalMessage (p : UpperPosition S) (root : H) : Message S M H p.1 := by
  simpa [Message, p.2] using root

/-- Fixed retry metadata for the child root certified by one upper one-time key. -/
@[expose] def certificateResult (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S) (p : UpperPosition S) :
    IncomparableEncoding.IndexedResult R S.v (2 ^ S.w) :=
  componentResult family plan sk p.1
    (internalMessage p (componentRoot hash sk.seed sk.endpoints (childTree S p)))
    (sk.upperCoins p)

/-- The optional certificate is a deterministic function of its fixed child root and tape.
A failed fixed certificate remains failed on every signing request. -/
@[expose] def certificate (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S) (p : UpperPosition S) :
    Option (GXMSS.Signature R H S.h S.v) :=
  (certificateResult hash family plan sk p).output.map (componentSignature hash sk p.1)

/-- The global epoch's bottom one-time coordinate. -/
@[expose] def bottomPosition (S : Shape) (ep : Epoch S) : OTSPosition S :=
  positionAt S ep ⟨0, S.d_pos⟩

/-- The positive layer corresponding to an upper-signature array index. -/
@[expose] def upperLayer (S : Shape) (i : Fin (S.d - 1)) : Fin S.d :=
  ⟨i.val + 1, by have := i.isLt; have := S.d_pos; omega⟩

/-- The internal one-time coordinate used by an epoch at one positive layer. -/
@[expose] def upperPositionAt (S : Shape) (ep : Epoch S) (i : Fin (S.d - 1)) :
    UpperPosition S :=
  ⟨positionAt S ep (upperLayer S i), by simp [upperLayer]⟩

/-- Interpret an application message at the selected bottom coordinate. -/
@[expose] def bottomMessage (ep : Epoch S) (msg : M) :
    Message S M H (bottomPosition S ep) := by
  simpa [Message, bottomPosition] using msg

/-- Deterministic signing from explicit fresh bottom coins and persistent upper tapes.
Option sequencing stops at the first failed internal certificate. -/
@[expose] def signWithCoins (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) : Option (Signature R H S) := do
  let wr ← (componentResult family sampling.bottom sk (bottomPosition S ep)
    (bottomMessage ep msg) coins).output
  let upper ← Fin.mOfFn (S.d - 1) fun i =>
    certificate hash family sampling.internal sk (upperPositionAt S ep i)
  pure ⟨componentSignature hash sk (bottomPosition S ep) wr, upper⟩

/-- Fresh bottom retry coins are drawn once per eligible global request. -/
@[expose] def sign (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S) (ep : Epoch S) (msg : M) :
    ProbComp (Option (Signature R H S)) :=
  (signWithCoins hash family sampling sk ep msg) <$> sampling.sampleBottom

/-- Re-encode and recover one component root from arbitrary signature data. -/
@[expose] def recoverComponent (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP) (p : OTSPosition S)
    (msg : Message S M H p) (sig : GXMSS.Signature R H S.h S.v) : Option H := do
  let word ← family.value p pp msg sig.randomizer
  pure ((hash.componentHash p.1).recoverRoot pp p.2
    (fun i => (hash.componentHash p.1).chain pp p.2 i (word i)
      (2 ^ S.w - 1 - (word i).val) (sig.ots i)) sig.path)

/-- Recover through a bounded layer, preserving every optional re-encoding failure. -/
@[expose] def recoverThrough (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP) (ep : Epoch S) (msg : M)
    (sig : Signature R H S) : (layer : ℕ) → layer < S.d → Option H
  | 0, _ => recoverComponent hash family pp (bottomPosition S ep)
      (bottomMessage ep msg) sig.bottom
  | layer + 1, hlayer => do
      let child ← recoverThrough hash family pp ep msg sig layer (by omega)
      let i : Fin (S.d - 1) := ⟨layer, by omega⟩
      recoverComponent hash family pp (upperPositionAt S ep i).1
        (internalMessage (upperPositionAt S ep i) child) (sig.upper i)

/-- Recover the top root from all layer signatures, without restricting adversarial inputs. -/
@[expose] def recoverRoot (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP) (ep : Epoch S) (msg : M)
    (sig : Signature R H S) : Option H :=
  recoverThrough hash family pp ep msg sig (S.d - 1) (by have := S.d_pos; omega)

/-- All-input verification rejects every failed layer and compares the final recovered root. -/
@[expose] def verify [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pk : GXMSS.PublicKey PP H)
    (ep : Epoch S) (msg : M) (sig : Signature R H S) : Bool :=
  decide (recoverRoot hash family pk.seed ep msg sig = some pk.root)

/-- The synchronized forest scheme has a single global first-request history and parameterless
key generation. A returned bottom or internal exhaustion consumes its requested global epoch. -/
@[expose] noncomputable def scheme [SampleableType H] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) :
    SyncSignatureAlg ProbComp M (GXMSS.PublicKey PP H)
      (SecretKey PP H sampling.internal.Coins S) (Signature R H S) (Epoch S) where
  keygen := keygen hash sampling
  sign := sign hash family sampling
  verify := verify hash family

end GXMSS.Hypertree
