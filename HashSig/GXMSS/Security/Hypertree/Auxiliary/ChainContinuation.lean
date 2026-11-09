/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Scheme
public import HashSig.GXMSS.Hypertree.Completeness
public import HashSig.GXMSS.Security.Auxiliary.ChainContinuation
import all HashSig.GXMSS.Scheme

/-!
# Forest chain continuations

All component roots, paths, internal messages and fixed-tape retry results are prepared from
the complete endpoint table. Signature materialization reads chain prefixes separately.
The resulting instance of the common continuation kernel recomputes ancestor certificates
and retains every fixed retry failure. Its equations concern deterministic signing outputs;
adaptive transcript and probability transports require separate invariants.
-/

public section

namespace GXMSS.Hypertree.Security.ChainContinuation

open Encoding

variable {PP T X H M R : Type} {S : Shape}

/-- The common chain recurrence at every full forest coordinate. -/
@[expose] def chainFamily (hash : HashInstance PP T X H S) (pp : PP) :
    GXMSS.Reductions.ChainContinuation.ChainFamily (OTSPosition S) H S.v where
  chain := fun p => (hash.componentHash p.1).chain pp p.2
  chain_zero := fun p => (hash.componentHash p.1).chain_zero pp p.2
  chain_add := fun p => (hash.componentHash p.1).chain_add pp p.2

/-- Honest chain prefixes at all forest coordinates. -/
@[expose] def honestPrefixes (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (p : OTSPosition S) (i : Fin S.v) (k : ℕ) : H :=
  (chainFamily hash pp).chain p i 0 k (starts p i)

/-- Every component endpoint after one global chain splice. -/
@[expose] def spliceEndpoints (hash : HashInstance PP T X H S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) : OTSPosition S → Fin S.v → H :=
  GXMSS.Reductions.ChainContinuation.spliceEndpoints (chainFamily hash pp)
    (2 ^ S.w - 1) selected i cut answer starts

/-- All signature-prefix reads under one global splice. -/
@[expose] def splicePrefixes (hash : HashInstance PP T X H S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) : OTSPosition S → Fin S.v → ℕ → H :=
  GXMSS.Reductions.ChainContinuation.spliceValue (chainFamily hash pp) selected i cut answer starts

/-- At its own cut the selected prefix reader returns the supplied challenge response. -/
theorem splicePrefixes_selected_cut (hash : HashInstance PP T X H S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) :
    splicePrefixes hash pp selected i cut answer starts selected i (cut + 1) = answer :=
  GXMSS.Reductions.ChainContinuation.spliceEndpoints_selected_final
    (chainFamily hash pp) selected i cut answer starts

/-- Metadata derived from the entire endpoint table before any chain-prefix reveals. -/
structure Metadata (R H : Type) (S : Shape) where
  /-- Actual roots of every component tree. -/
  roots : TreePosition S → H
  /-- Actual leaf-first paths at every one-time coordinate. -/
  paths : OTSPosition S → Fin S.h → H
  /-- Complete fixed-tape retry results, including exhaustion and consumed randomizers. -/
  internalResults : UpperPosition S → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w)

/-- Prepare all ancestor messages, paths and fixed retry results from endpoints and fixed coins. -/
@[expose] def prepare (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (plan : RetryPlan R) (pp : PP) (ends : OTSPosition S → Fin S.v → H)
    (coins : UpperPosition S → plan.Coins) : Metadata R H S where
  roots := componentRoot hash pp ends
  paths := fun p => (hash.componentHash p.1).authPath pp (fun ep => ends (p.1, ep)) p.2
  internalResults := fun p => plan.run (family.atEpoch p.1 (Fin S.branching)) pp
    (internalMessage p (componentRoot hash pp ends (childTree S p))) p.val.2 (coins p)

/-- Fresh bottom retry metadata is independent of all secret chain starts and endpoints. -/
@[expose] def bottomResult (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (pp : PP) (ep : Epoch S) (msg : M) (coins : plan.Coins) :
    IncomparableEncoding.IndexedResult R S.v (2 ^ S.w) :=
  plan.run (family.atEpoch (bottomPosition S ep) (Fin S.branching)) pp
    (bottomMessage ep msg) (bottomPosition S ep).2 coins

/-- Materialize a component using the prepared path and an explicit prefix reader. -/
@[expose] def component (metadata : Metadata R H S)
    (prefixes : OTSPosition S → Fin S.v → ℕ → H) (p : OTSPosition S)
    (wr : Codeword S.v (2 ^ S.w) × R) : GXMSS.Signature R H S.h S.v :=
  ⟨wr.2, fun i => prefixes p i (wr.1 i), metadata.paths p⟩

/-- Canonical private certificate options use the current prefix reader and fixed retry results. -/
@[expose] def canonicalReferences (metadata : Metadata R H S)
    (prefixes : OTSPosition S → Fin S.v → ℕ → H) :
    UpperPosition S → Option (GXMSS.Signature R H S.h S.v) := fun p =>
  (metadata.internalResults p).output.map (component metadata prefixes p.1)

/-- Materialize the actual optional forest signature, preserving bottom and internal exhaustion. -/
@[expose] def materialize (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pp : PP) (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins)
    (metadata : Metadata R H S) (prefixes : OTSPosition S → Fin S.v → ℕ → H) :
    Option (Signature R H S) := do
  let wr ← (bottomResult family sampling.bottom pp ep msg coins).output
  let upper ← Fin.mOfFn (S.d - 1) fun i =>
    (metadata.internalResults (upperPositionAt S ep i)).output.map
      (component metadata prefixes (upperPositionAt S ep i).1)
  pure ⟨component metadata prefixes (bottomPosition S ep) wr, upper⟩

/-- A prefix read needed by a successful component of the attempted forest signature.
This overapproximation includes later successful certificates after an earlier failure. -/
@[expose] def RawReads (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pp : PP) (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins)
    (metadata : Metadata R H S) (p : OTSPosition S) (i : Fin S.v) (position : ℕ) : Prop :=
  (p = bottomPosition S ep ∧ ∃ wr,
    (bottomResult family sampling.bottom pp ep msg coins).output = some wr ∧
      position = (wr.1 i).val) ∨
  ∃ k : Fin (S.d - 1), p = (upperPositionAt S ep k).1 ∧ ∃ wr,
    (metadata.internalResults (upperPositionAt S ep k)).output = some wr ∧
      position = (wr.1 i).val

/-- Equality at a component's actual word positions preserves its entire signature. -/
theorem component_eq_of_prefix_eq (metadata : Metadata R H S)
    (left right : OTSPosition S → Fin S.v → ℕ → H) (p : OTSPosition S)
    (wr : Codeword S.v (2 ^ S.w) × R)
    (h : ∀ i, left p i (wr.1 i) = right p i (wr.1 i)) :
    component metadata left p wr = component metadata right p wr := by
  apply congrArg (fun f : Fin S.v → H => (⟨wr.2, f, metadata.paths p⟩ :
    GXMSS.Signature R H S.h S.v))
  funext i
  exact h i

/-- The actual forest materializer depends only on its declared prefix reads. -/
private theorem materialize_eq_of_rawPrefix_eq (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (pp : PP) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) (metadata : Metadata R H S)
    (left right : OTSPosition S → Fin S.v → ℕ → H)
    (h : ∀ p i position, RawReads family sampling pp ep msg coins metadata p i position →
      left p i position = right p i position) :
    materialize family sampling pp ep msg coins metadata left =
      materialize family sampling pp ep msg coins metadata right := by
  have hupper : (fun k : Fin (S.d - 1) =>
        (metadata.internalResults (upperPositionAt S ep k)).output.map
          (component metadata left (upperPositionAt S ep k).1)) =
      (fun k : Fin (S.d - 1) =>
        (metadata.internalResults (upperPositionAt S ep k)).output.map
          (component metadata right (upperPositionAt S ep k).1)) := by
    funext k
    cases hresult : (metadata.internalResults (upperPositionAt S ep k)).output with
    | none => rfl
    | some wr =>
        simp only [Option.map_some]
        apply congrArg some
        apply component_eq_of_prefix_eq
        intro i
        exact h _ i _ (Or.inr ⟨k, rfl, wr, hresult, rfl⟩)
  unfold materialize
  rw [hupper]
  cases hbottom : (bottomResult family sampling.bottom pp ep msg coins).output with
  | none => rfl
  | some wr =>
      have hcomponent := component_eq_of_prefix_eq metadata left right
        (bottomPosition S ep) wr (fun i => h _ i _ (Or.inl ⟨rfl, wr, hbottom, rfl⟩))
      simp only [Option.bind_eq_bind, Option.bind_some]
      simp_rw [hcomponent]

/-- Optional finite sequencing commutes with coordinate-wise total materialization. -/
theorem fin_mOfFn_option_map {A B : Type} (n : ℕ) (f : Fin n → Option A)
    (g : (i : Fin n) → A → B) :
    Fin.mOfFn n (fun i => (f i).map (g i)) =
      (Fin.mOfFn n f).map (fun values i => g i (values i)) := by
  induction n with
  | zero =>
      apply congrArg some
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Fin.mOfFn]
      cases hhead : f 0 with
      | none => rfl
      | some head =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
          rw [ih (fun i => f i.succ) (fun i => g i.succ)]
          cases htail : Fin.mOfFn n (fun i => f i.succ) with
          | none => rfl
          | some tail =>
              apply congrArg some
              funext i
              cases i using Fin.cases <;> rfl

/-- Select the complete word tuple from one bottom result and the fixed upper table. -/
@[expose] def wordsFromResult (metadata : Metadata R H S) (ep : Epoch S)
    (result : IncomparableEncoding.IndexedResult R S.v (2 ^ S.w)) :
    Option ((Codeword S.v (2 ^ S.w) × R) ×
      (Fin (S.d - 1) → Codeword S.v (2 ^ S.w) × R)) := do
  let bottom ← result.output
  let upper ← Fin.mOfFn (S.d - 1) fun i =>
    (metadata.internalResults (upperPositionAt S ep i)).output
  pure (bottom, upper)

/-- Successful word tuples are selected entirely from retry metadata, without prefix values. -/
@[expose] def wordResults (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pp : PP) (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins)
    (metadata : Metadata R H S) :
    Option ((Codeword S.v (2 ^ S.w) × R) ×
      (Fin (S.d - 1) → Codeword S.v (2 ^ S.w) × R)) :=
  wordsFromResult metadata ep (bottomResult family sampling.bottom pp ep msg coins)

/-- A selected full word tuple retains the exact successful bottom and upper results. -/
theorem wordsFromResult_success (metadata : Metadata R H S) (ep : Epoch S)
    (result : IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (words : (Codeword S.v (2 ^ S.w) × R) ×
      (Fin (S.d - 1) → Codeword S.v (2 ^ S.w) × R))
    (h : wordsFromResult metadata ep result = some words) :
    result.output = some words.1 ∧ ∀ i,
      (metadata.internalResults (upperPositionAt S ep i)).output = some (words.2 i) := by
  cases hbottom : result.output with
  | none => simp [wordsFromResult, hbottom] at h
  | some bottom =>
      cases hupper : Fin.mOfFn (S.d - 1) (fun i =>
          (metadata.internalResults (upperPositionAt S ep i)).output) with
      | none => simp [wordsFromResult, hbottom, hupper] at h
      | some upper =>
          have heq : (bottom, upper) = words := by
            simpa [wordsFromResult, hbottom, hupper] using h
          subst words
          exact ⟨rfl, (fin_mOfFn_eq_some_iff _ upper).mp hupper⟩

/-- Full signing success is determined by the prepared retry metadata and bottom coins. -/
@[expose] def FullSuccess (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pp : PP) (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins)
    (metadata : Metadata R H S) : Prop :=
  (wordResults family sampling pp ep msg coins metadata).isSome = true

/-- Prefix values are only disclosed when the entire optional signature succeeds. -/
@[expose] def Reads (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pp : PP) (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins)
    (metadata : Metadata R H S) (p : OTSPosition S) (i : Fin S.v) (position : ℕ) : Prop :=
  FullSuccess family sampling pp ep msg coins metadata ∧
    RawReads family sampling pp ep msg coins metadata p i position

/-- The optional signing result factors through metadata-only word selection. -/
theorem materialize_eq_map_wordResults (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (pp : PP) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) (metadata : Metadata R H S)
    (prefixes : OTSPosition S → Fin S.v → ℕ → H) :
    materialize family sampling pp ep msg coins metadata prefixes =
      (wordResults family sampling pp ep msg coins metadata).map (fun words =>
        (⟨component metadata prefixes (bottomPosition S ep) words.1,
          fun k => component metadata prefixes (upperPositionAt S ep k).1 (words.2 k)⟩ :
          Signature R H S)) := by
  unfold materialize wordResults wordsFromResult
  rw [fin_mOfFn_option_map]
  cases hbottom : (bottomResult family sampling.bottom pp ep msg coins).output with
  | none => rfl
  | some bottom =>
      cases hupper : Fin.mOfFn (S.d - 1) (fun i =>
          (metadata.internalResults (upperPositionAt S ep i)).output) with
      | none => rfl
      | some upper => rfl

/-- A failed full signing attempt reveals no prefixes, including a successful bottom retry. -/
theorem materialize_eq_none_of_not_fullSuccess (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (pp : PP) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) (metadata : Metadata R H S)
    (prefixes : OTSPosition S → Fin S.v → ℕ → H)
    (h : ¬FullSuccess family sampling pp ep msg coins metadata) :
    materialize family sampling pp ep msg coins metadata prefixes = none := by
  rw [materialize_eq_map_wordResults]
  cases hout : wordResults family sampling pp ep msg coins metadata with
  | none => rfl
  | some words => exact False.elim (h (by simp [FullSuccess, hout]))

/-- The actual optional forest answer depends only on full-return disclosed prefix reads. -/
theorem materialize_eq_of_prefix_eq (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (pp : PP) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) (metadata : Metadata R H S)
    (left right : OTSPosition S → Fin S.v → ℕ → H)
    (h : ∀ p i position, Reads family sampling pp ep msg coins metadata p i position →
      left p i position = right p i position) :
    materialize family sampling pp ep msg coins metadata left =
      materialize family sampling pp ep msg coins metadata right := by
  by_cases hsuccess : FullSuccess family sampling pp ep msg coins metadata
  · apply materialize_eq_of_rawPrefix_eq
    intro p i position hraw
    exact h p i position ⟨hsuccess, hraw⟩
  · rw [materialize_eq_none_of_not_fullSuccess family sampling pp ep msg coins metadata left
      hsuccess, materialize_eq_none_of_not_fullSuccess family sampling pp ep msg coins metadata
      right hsuccess]

/-- The concrete arbitrary-depth signing continuation instantiates the common kernel. -/
@[expose] def continuation (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pp : PP) (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins) :
    GXMSS.Reductions.ChainContinuation.EndpointContinuation (OTSPosition S) H
      (UpperPosition S → sampling.internal.Coins)
      (Metadata R H S) (Option (Signature R H S)) S.v where
  prepare := prepare hash family sampling.internal pp
  materialize := materialize family sampling pp ep msg coins
  reads := Reads family sampling pp ep msg coins
  materialize_congr := materialize_eq_of_prefix_eq family sampling pp ep msg coins

/-- Prepared internal results equal the scheme's exact fixed-certificate retry results. -/
theorem prepare_internalResults (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S) (p : UpperPosition S) :
    (prepare hash family plan sk.seed sk.endpoints sk.upperCoins).internalResults p =
      certificateResult hash family plan sk p := rfl

/-- Prepared paths and honest prefixes recover the scheme's component signature exactly. -/
theorem component_honest (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S) (p : OTSPosition S)
    (wr : Codeword S.v (2 ^ S.w) × R) :
    component (prepare hash family plan sk.seed sk.endpoints sk.upperCoins)
      (honestPrefixes hash sk.seed sk.starts) p wr = componentSignature hash sk p wr := rfl

/-- Honest canonical private references are exactly the scheme's fixed certificates. -/
theorem canonicalReferences_honest (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S) :
    canonicalReferences (prepare hash family plan sk.seed sk.endpoints sk.upperCoins)
      (honestPrefixes hash sk.seed sk.starts) = certificate hash family plan sk := rfl

/-- Honest materialization is the actual explicit-coin signing algorithm, including failure. -/
theorem materialize_honest (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) :
    materialize family sampling sk.seed ep msg coins
      (prepare hash family sampling.internal sk.seed sk.endpoints sk.upperCoins)
      (honestPrefixes hash sk.seed sk.starts) =
      signWithCoins hash family sampling sk ep msg coins := rfl

/-- Assemble the actual full forest signature after one selected chain splice. -/
@[expose] def spliceSign (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins) : Option (Signature R H S) :=
  materialize family sampling pp ep msg coins
    (prepare hash family sampling.internal pp
      (spliceEndpoints hash pp selected i cut answer starts) upperCoins)
    (splicePrefixes hash pp selected i cut answer starts)

/-- An honest cut response recovers every forest endpoint. -/
theorem spliceEndpoints_honest (hash : HashInstance PP T X H S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ)
    (starts : OTSPosition S → Fin S.v → H) :
    spliceEndpoints hash pp selected i cut
      ((chainFamily hash pp).chain selected i 0 (cut + 1) (starts selected i)) starts =
      endpoints hash pp starts :=
  GXMSS.Reductions.ChainContinuation.spliceEndpoints_honest
    (chainFamily hash pp) (2 ^ S.w - 1) selected i cut starts

/-- An honest cut response recovers every forest chain-prefix read. -/
theorem splicePrefixes_honest (hash : HashInstance PP T X H S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ)
    (starts : OTSPosition S → Fin S.v → H) :
    splicePrefixes hash pp selected i cut
      ((chainFamily hash pp).chain selected i 0 (cut + 1) (starts selected i)) starts =
      honestPrefixes hash pp starts := by
  funext p j position
  exact GXMSS.Reductions.ChainContinuation.spliceValue_honest
    (chainFamily hash pp) selected i cut starts p j position

/-- The full honest splice equals actual signing with the original explicit key and fixed tapes. -/
theorem spliceSign_honest (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins) :
    spliceSign hash family sampling pp selected i cut
      ((chainFamily hash pp).chain selected i 0 (cut + 1) (starts selected i))
      starts upperCoins ep msg coins =
      signWithCoins hash family sampling
        ⟨pp, starts, endpoints hash pp starts, upperCoins⟩ ep msg coins := by
  unfold spliceSign
  rw [spliceEndpoints_honest, splicePrefixes_honest]
  exact materialize_honest hash family sampling
    ⟨pp, starts, endpoints hash pp starts, upperCoins⟩ ep msg coins

/-- Equal endpoint tables and the same tapes preserve all forest metadata. -/
theorem prepare_eq_of_endpoints_eq (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (left right : OTSPosition S → Fin S.v → H) (coins : UpperPosition S → plan.Coins)
    (h : left = right) : prepare hash family plan pp left coins =
      prepare hash family plan pp right coins := congrArg (prepare hash family plan pp · coins) h

/-- Zero-cut metadata ignores the old selected start, including internal failure traces. -/
theorem prepare_zero_start_update (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) (replacement : H)
    (coins : UpperPosition S → plan.Coins) (hn : 0 < 2 ^ S.w - 1) :
    prepare hash family plan pp (spliceEndpoints hash pp selected i 0 answer
      (Function.update starts selected (Function.update (starts selected) i replacement))) coins =
      prepare hash family plan pp (spliceEndpoints hash pp selected i 0 answer starts) coins := by
  apply prepare_eq_of_endpoints_eq
  exact GXMSS.Reductions.ChainContinuation.spliceEndpoints_zero_start_update
    (chainFamily hash pp) (2 ^ S.w - 1) selected i answer starts replacement hn

/-- Adjacent chain splices preserve the entire recomputed metadata table. -/
theorem prepare_advance (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) (coins : UpperPosition S → plan.Coins)
    (hn : cut + 2 ≤ 2 ^ S.w - 1) :
    prepare hash family plan pp (spliceEndpoints hash pp selected i cut answer starts) coins =
      prepare hash family plan pp (spliceEndpoints hash pp selected i (cut + 1)
        ((chainFamily hash pp).chain selected i (cut + 1) 1 answer) starts) coins := by
  exact congrArg (fun ends => prepare hash family plan pp ends coins)
    (GXMSS.Reductions.ChainContinuation.spliceEndpoints_advance (chainFamily hash pp) (2 ^ S.w - 1)
      selected i cut answer starts hn)

/-- Every surviving component read past both cuts preserves the whole optional forest signature. -/
theorem spliceSign_advance (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins)
    (hn : cut + 2 ≤ 2 ^ S.w - 1)
    (hsafe : ∀ p j position,
      Reads family sampling pp ep msg coins
        (prepare hash family sampling.internal pp
          (spliceEndpoints hash pp selected i cut answer starts) upperCoins) p j position →
      p = selected → j = i → cut + 2 ≤ position) :
    spliceSign hash family sampling pp selected i cut answer starts upperCoins ep msg coins =
      spliceSign hash family sampling pp selected i (cut + 1)
        ((chainFamily hash pp).chain selected i (cut + 1) 1 answer)
        starts upperCoins ep msg coins :=
  (continuation hash family sampling pp ep msg coins).materialize_splice_advance
    (chainFamily hash pp) (2 ^ S.w - 1) selected i cut answer starts upperCoins hn hsafe

/-- Safe zero-cut materialization ignores the old selected start, including all ancestor results. -/
theorem spliceSign_zero_start_update (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) (replacement : H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins) (hn : 0 < 2 ^ S.w - 1)
    (hsafe : ∀ p j position,
      Reads family sampling pp ep msg coins
        (prepare hash family sampling.internal pp
          (spliceEndpoints hash pp selected i 0 answer starts) upperCoins) p j position →
      p = selected → j = i → 0 < position) :
    spliceSign hash family sampling pp selected i 0 answer
      (Function.update starts selected (Function.update (starts selected) i replacement))
      upperCoins ep msg coins =
    spliceSign hash family sampling pp selected i 0 answer starts upperCoins ep msg coins :=
  (continuation hash family sampling pp ep msg coins).materialize_zero_start_update
    (chainFamily hash pp) (2 ^ S.w - 1) selected i answer starts replacement upperCoins hn hsafe

/-- A splice in another component leaves this component root unchanged. -/
theorem componentRoot_splice_other_tree (hash : HashInstance PP T X H S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) (tree : TreePosition S)
    (hne : tree ≠ selected.1) :
    componentRoot hash pp (spliceEndpoints hash pp selected i cut answer starts) tree =
      componentRoot hash pp (endpoints hash pp starts) tree := by
  apply congrArg ((hash.componentHash tree).merkleRoot pp)
  funext ep j
  have ht : ¬((tree, ep) = selected ∧ j = i) := fun h => hne (congrArg Prod.fst h.1)
  simp only [spliceEndpoints, GXMSS.Reductions.ChainContinuation.spliceEndpoints,
    GXMSS.Reductions.ChainContinuation.spliceValue, ht, ↓reduceDIte, endpoints, chainFamily]

/-- The child certified by an upper OTS is in the strictly preceding layer. -/
theorem childTree_ne_selected_tree (p : UpperPosition S) : childTree S p ≠ p.val.1 := by
  intro h
  have hl := congrArg (fun tree : TreePosition S => tree.1.val) h
  have hp := p.property
  rw [childTree_layer_val] at hl
  omega

/-- Splicing an internal OTS never changes its own certified child-root message. -/
theorem selected_internal_message_locality (hash : HashInstance PP T X H S) (pp : PP)
    (selected : UpperPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) :
    internalMessage (M := M) selected
      (componentRoot hash pp (spliceEndpoints hash pp selected.1 i cut answer starts)
        (childTree S selected)) =
    internalMessage (M := M) selected
      (componentRoot hash pp (endpoints hash pp starts) (childTree S selected)) := by
  rw [componentRoot_splice_other_tree hash pp selected.1 i cut answer starts
    (childTree S selected) (childTree_ne_selected_tree selected)]

/-- The selected internal retry result is invariant under its own splice, including failure. -/
theorem selected_internal_result_locality (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (selected : UpperPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) (coins : UpperPosition S → plan.Coins) :
    (prepare hash family plan pp (spliceEndpoints hash pp selected.1 i cut answer starts)
      coins).internalResults selected =
    (prepare hash family plan pp (endpoints hash pp starts) coins).internalResults selected := by
  dsimp only [prepare]
  rw [selected_internal_message_locality hash pp selected i cut answer starts]

end GXMSS.Hypertree.Security.ChainContinuation
