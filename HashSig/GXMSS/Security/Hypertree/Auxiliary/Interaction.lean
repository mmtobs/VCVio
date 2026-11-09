/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.FamilyEncoding
public import HashSig.GXMSS.Hypertree.Completeness
import all HashSig.GXMSS.Hypertree.Scheme
public import ToMathlib.Control.Monad.Fold
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Native hypertree source interaction and private certificate ledger

The actual synchronized interaction retains the generated secret key and first-request history.
Its private upper table contains every fixed certificate's full retry result, including failures
at coordinates never disclosed by signing. This table is separate from any disclosed partial prefix.
-/

public section

namespace GXMSS.Hypertree.Security

open Encoding OracleComp OracleSpec

/-- The actual adaptive synchronized-signature adversary over global epochs. -/
abbrev SchemeAdversary (PP H M R : Type) (S : Shape) :=
  SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch S) M
    (Signature R H S)

/-- Complete eager private retry metadata at the internal signing coordinates. -/
abbrev UpperResults (R : Type) (S : Shape) :=
  UpperPosition S → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w)

/-- Complete retry metadata for one first eligible bottom signing request. -/
structure BottomAttempt (M R : Type) (S : Shape) where
  /-- Consumed global epoch. -/
  epoch : Epoch S
  /-- First requested application message. -/
  message : M
  /-- Actual complete bottom retry result, retained also after an upper certificate fails. -/
  result : IncomparableEncoding.IndexedResult R S.v (2 ^ S.w)

/-- Full internal source result; raw upper coins remain private to this enriched result. -/
structure Result (PP H M R Coins : Type) (S : Shape) where
  /-- The public root and seed given to the adversary. -/
  pk : GXMSS.PublicKey PP H
  /-- Actual generated raw key, including every fixed internal tape. -/
  sk : SecretKey PP H Coins S
  /-- Candidate global epoch, message and complete signature. -/
  forgery : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S)
  /-- Actual first signing-request record at each global epoch. -/
  history : SyncSignatureUnforgeability.History (Epoch S) M (Signature R H S)
  /-- Private eager certificate results, including all exhaustion and attempt metadata. -/
  upperResults : UpperResults R S
  /-- Full bottom attempts at first eligible global requests, in their actual request order. -/
  bottomAttempts : List (BottomAttempt M R S)

variable {PP T X H M R Coins : Type} {S : Shape}

/-- The complete fixed-certificate table, determined without fresh draws by the generated key. -/
@[expose] def upperResults (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S) : UpperResults R S :=
  certificateResult hash family plan sk

/-- Native signing state: actual first-request history and private full bottom attempts. -/
abbrev NativeState (M H R : Type) (S : Shape) :=
  SyncSignatureUnforgeability.History (Epoch S) M (Signature R H S) ×
    List (BottomAttempt M R S)

/-- One first-request handler samples coins once and records the result of the supplied attempt
observer. The signature callback receives exactly those same coins. -/
@[expose] def signingOracleWithAttempts (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S)) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch S) M (Signature R H S))
      (StateT (NativeState M H R S) ProbComp) := fun q state =>
  match state.1 q.1 with
  | some _ => pure (none, state)
  | none => do
      let coins ← sample
      let result := attempt q.1 q.2 coins
      let answer := signer q.1 q.2 coins
      pure (answer, Function.update state.1 q.1 (some (q.2, answer)),
        state.2 ++ [⟨q.1, q.2, result⟩])

/-- The actual signing handler records complete bottom metadata and uses the same coins for the
full optional signature. Duplicates make no draw and retain all first-request data. -/
@[expose] def nativeSigningOracle (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch S) M (Signature R H S))
      (StateT (NativeState M H R S) ProbComp) :=
  signingOracleWithAttempts sampling.sampleBottom
    (fun ep msg coins => componentResult family sampling.bottom sk (bottomPosition S ep)
      (bottomMessage ep msg) coins)
    (signWithCoins hash family sampling sk)

/-- Ambient private randomness is unchanged by private attempt recording. -/
@[expose] def nativeOracles (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)) (StateT (NativeState M H R S) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (NativeState M H R S) ProbComp) + nativeSigningOracle hash family sampling sk

/-- The adopted synchronized handler at fixed keys, without private enrichment. -/
@[expose] noncomputable def sourceOracles [SampleableType H] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (sk : SecretKey PP H sampling.internal.Coins S) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S))
      (StateT (SyncSignatureUnforgeability.History (Epoch S) M (Signature R H S)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History (Epoch S) M (Signature R H S)) ProbComp) +
      SyncSignatureUnforgeability.signingOracle (scheme hash family sampling) sk

/-- Each enriched query projects exactly to the actual synchronized signing handler. -/
theorem nativeOracles_proj [SampleableType H] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (sk : SecretKey PP H sampling.internal.Coins S)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)).Domain) (state : NativeState M H R S) :
    Prod.map id Prod.fst <$> (nativeOracles hash family sampling sk q).run state =
      (sourceOracles hash family sampling sk q).run state.1 := by
  cases q with
  | inl uniform =>
    simp [nativeOracles, sourceOracles, map_eq_bind_pure_comp, bind_assoc]
  | inr q =>
    rcases q with ⟨ep, msg⟩
    change Prod.map id Prod.fst <$> nativeSigningOracle hash family sampling sk (ep, msg) state =
      SyncSignatureUnforgeability.signingOracle (scheme hash family sampling) sk (ep, msg) state.1
    cases hused : state.1 ep with
    | none =>
      simp [nativeSigningOracle, signingOracleWithAttempts,
        SyncSignatureUnforgeability.signingOracle, scheme, sign, hused,
        map_eq_bind_pure_comp, bind_assoc]
    | some first =>
      simp [nativeSigningOracle, signingOracleWithAttempts,
        SyncSignatureUnforgeability.signingOracle, hused]

/-- Forgetting private bottom attempts commutes with the complete adaptive source interaction. -/
theorem native_run_proj [SampleableType H] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (sk : SecretKey PP H sampling.internal.Coins S)
    {α : Type}
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Signature R H S)) α) (state : NativeState M H R S) :
    Prod.map id Prod.fst <$> (simulateQ (nativeOracles hash family sampling sk) program).run state =
      (simulateQ (sourceOracles hash family sampling sk) program).run state.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (nativeOracles_proj hash family sampling sk) program state

/-- An internal source interaction under fixed generated keys. -/
@[expose] noncomputable def runWithKeys
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S) :
    ProbComp (Result PP H M R sampling.internal.Coins S) := do
  let (forgery, state) ← (simulateQ (nativeOracles hash family sampling sk) (adv.forge pk)).run
    (SyncSignatureUnforgeability.emptyHistory, [])
  pure ⟨pk, sk, forgery, state.1, upperResults hash family sampling.internal sk, state.2⟩

/-- Actual parameterless key generation followed by the native synchronized interaction. -/
@[expose] noncomputable def sourceProgram [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) :
    ProbComp (Result PP H M R sampling.internal.Coins S) := do
  let (pk, sk) ← keygen hash sampling
  runWithKeys hash family sampling adv pk sk

/-- Forget exactly the private key and eager private certificate table. -/
@[expose] def sourceObservation (out : Result PP H M R Coins S) :
    SyncSignatureUnforgeability.ExperimentResult (GXMSS.PublicKey PP H) (Epoch S) M
      (Signature R H S) :=
  (out.pk, out.forgery, out.history)

/-- The private enrichment leaves the actual returned interaction unchanged. -/
theorem sourceProgram_map_eq_interaction [SampleableType H] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) :
    sourceObservation <$> sourceProgram hash family sampling adv =
      SyncSignatureUnforgeability.interaction (scheme hash family sampling) adv := by
  unfold sourceProgram SyncSignatureUnforgeability.interaction
  simp only [map_bind]
  apply bind_congr
  intro generated
  change sourceObservation <$> runWithKeys hash family sampling adv generated.1 generated.2 =
    (do
      let result ← (simulateQ (sourceOracles hash family sampling generated.2)
        (adv.forge generated.1)).run SyncSignatureUnforgeability.emptyHistory
      pure (generated.1, result.1, result.2))
  rw [← native_run_proj hash family sampling generated.2 (adv.forge generated.1)
    (SyncSignatureUnforgeability.emptyHistory, [])]
  simp [runWithKeys, sourceObservation, map_eq_bind_pure_comp, bind_assoc, Prod.map]


/-- Actual strong-pair freshness and verification observed on an enriched source result. -/
@[expose] noncomputable def sourceStrongObservation [SampleableType H] [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (out : Result PP H M R sampling.internal.Coins S) : Bool :=
  SyncSignatureUnforgeability.strongValid (scheme hash family sampling) (sourceObservation out)

/-- The native successful-output measure of strong source wins. -/
noncomputable def sourceStrongOutputMeasure [SampleableType H] [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) :
    MeasureTheory.Measure Bool :=
  𝒟[sourceStrongObservation hash family sampling <$> sourceProgram hash family sampling adv]

/-- No private metadata is conditioned away when recovering the adopted strong experiment. -/
theorem sourceStrongOutputMeasure_eq_strongUnforgeableExp [SampleableType H] [DecidableEq H]
    [DecidableEq M] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) :
    sourceStrongOutputMeasure hash family sampling adv =
      SyncSignatureUnforgeability.strongUnforgeableExp (scheme hash family sampling)
        ProbCompRuntime.probComp adv := by
  simp only [sourceStrongOutputMeasure, SyncSignatureUnforgeability.strongUnforgeableExp,
    SyncSignatureUnforgeability.outputMeasure, ProbCompRuntime.probComp_evalDist]
  congr 1
  change (fun out => SyncSignatureUnforgeability.strongValid
    (scheme hash family sampling) (sourceObservation out)) <$>
      sourceProgram hash family sampling adv = _
  rw [← Functor.map_map, sourceProgram_map_eq_interaction]

/-- A component result is the coordinate's local encoder run on exactly the same coins. -/
theorem componentResult_eq_run (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H Coins S) (p : OTSPosition S) (msg : Message S M H p)
    (coins : plan.Coins) : componentResult family plan sk p msg coins =
      plan.run (family.component p) sk.seed msg () coins :=
  plan.run_eq_of_values_eq (family.atEpoch p (Fin S.branching)) (family.component p)
    sk.seed sk.seed msg msg p.2 () coins (fun _ => rfl)

/-- Every successful first record is the signature callback evaluated at one actual coin draw. -/
@[expose] def ReturnedHistory (sample : ProbComp Coins)
    (signer : Epoch S → M → Coins → Option (Signature R H S))
    (history : SyncSignatureUnforgeability.History (Epoch S) M (Signature R H S)) : Prop :=
  ∀ ep msg sig, history ep = some (msg, some sig) →
    ∃ coins ∈ support sample, signer ep msg coins = some sig

/-- Private attempt recording preserves exact callback witnesses for all successful records. -/
theorem signingOracleWithAttempts_preserves_returns (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S))
    (q : Epoch S × M) (state : NativeState M H R S)
    (hinv : ReturnedHistory sample signer state.1)
    (out : Option (Signature R H S) × NativeState M H R S)
    (hout : out ∈ support ((signingOracleWithAttempts sample attempt signer q).run state)) :
    ReturnedHistory sample signer out.2.1 := by
  rcases q with ⟨ep, msg⟩
  change out ∈ support (signingOracleWithAttempts sample attempt signer (ep, msg) state) at hout
  cases hused : state.1 ep with
  | some first =>
    simp only [signingOracleWithAttempts, hused, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact hinv
  | none =>
    simp only [signingOracleWithAttempts, hused, mem_support_bind_iff] at hout
    obtain ⟨coins, hcoins, hret⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hret
    subst out
    intro ep' msg' sig' hrecord
    by_cases heq : ep' = ep
    · subst ep'
      have hpair : msg = msg' ∧ signer ep msg coins = some sig' := by
        simpa [Function.update] using hrecord
      exact ⟨coins, hcoins, by simpa [hpair.1] using hpair.2⟩
    · exact hinv ep' msg' sig' (by simpa [Function.update, heq] using hrecord)

/-- Every private attempt retains the actual coin and its full synchronized-history answer. -/
@[expose] def AttemptsMatchHistory (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S))
    (state : NativeState M H R S) : Prop :=
  ∀ entry ∈ state.2, ∃ coins ∈ support sample,
    entry.result = attempt entry.epoch entry.message coins ∧
      state.1 entry.epoch = some (entry.message, signer entry.epoch entry.message coins)

/-- The single-coin handler preserves full attempt/history association even after full failure. -/
theorem signingOracleWithAttempts_preserves_attempts (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S))
    (q : Epoch S × M) (state : NativeState M H R S)
    (hinv : AttemptsMatchHistory sample attempt signer state)
    (out : Option (Signature R H S) × NativeState M H R S)
    (hout : out ∈ support ((signingOracleWithAttempts sample attempt signer q).run state)) :
    AttemptsMatchHistory sample attempt signer out.2 := by
  rcases q with ⟨ep, msg⟩
  change out ∈ support (signingOracleWithAttempts sample attempt signer (ep, msg) state) at hout
  cases hused : state.1 ep with
  | some first =>
    simp only [signingOracleWithAttempts, hused, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact hinv
  | none =>
    simp only [signingOracleWithAttempts, hused, mem_support_bind_iff] at hout
    obtain ⟨coins, hcoins, hret⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hret
    subst out
    intro entry hentry
    rcases List.mem_append.mp hentry with hold | hnew
    · obtain ⟨oldCoins, hsupport, hresult, hhistory⟩ := hinv entry hold
      have hne : entry.epoch ≠ ep := by
        intro heq
        rw [heq, hused] at hhistory
        contradiction
      exact ⟨oldCoins, hsupport, hresult, by simpa [Function.update, hne] using hhistory⟩
    · have heq : entry = (⟨ep, msg, attempt ep msg coins⟩ : BottomAttempt M R S) := by
        simpa using hnew
      subst entry
      exact ⟨coins, hcoins, rfl, by simp [Function.update]⟩

/-- A first-request handler never repeats an epoch in its private attempt log. -/
theorem signingOracleWithAttempts_preserves_nodup (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S))
    (q : Epoch S × M) (state : NativeState M H R S)
    (hinv : AttemptsMatchHistory sample attempt signer state)
    (hnd : (state.2.map BottomAttempt.epoch).Nodup)
    (out : Option (Signature R H S) × NativeState M H R S)
    (hout : out ∈ support ((signingOracleWithAttempts sample attempt signer q).run state)) :
    (out.2.2.map BottomAttempt.epoch).Nodup := by
  rcases q with ⟨ep, msg⟩
  change out ∈ support (signingOracleWithAttempts sample attempt signer (ep, msg) state) at hout
  cases hused : state.1 ep with
  | some first =>
    simp only [signingOracleWithAttempts, hused, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact hnd
  | none =>
    simp only [signingOracleWithAttempts, hused, mem_support_bind_iff] at hout
    obtain ⟨coins, _, hret⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hret
    subst out
    have hnot : ep ∉ state.2.map BottomAttempt.epoch := by
      intro hmem
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
      obtain ⟨_, _, _, hhistory⟩ := hinv entry hentry
      rw [heq, hused] at hhistory
      contradiction
    simpa only [List.map_append, List.map_singleton] using
      hnd.append (List.nodup_singleton ep) (List.disjoint_singleton.mpr hnot)

/-- Every actual fixed-key source run has distinct consumed epochs in its full bottom log. -/
theorem runWithKeys_bottomAttempts_nodup
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (runWithKeys hash family sampling adv pk sk)) :
    (out.bottomAttempts.map BottomAttempt.epoch).Nodup := by
  classical
  let attempt := fun ep msg coins => componentResult family sampling.bottom sk (bottomPosition S ep)
    (bottomMessage ep msg) coins
  let inv := fun state : NativeState M H R S =>
    AttemptsMatchHistory sampling.sampleBottom attempt
      (signWithCoins hash family sampling sk) state ∧
      (state.2.map BottomAttempt.epoch).Nodup
  have hpres : QueryImpl.PreservesInv (nativeOracles hash family sampling sk) inv := by
    intro q state hinv output houtput
    cases q with
    | inl uniform =>
      change output ∈ support
        ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at houtput
      obtain ⟨answer, _, hret⟩ := (mem_support_bind_iff _ _ _).mp houtput
      have heq := (mem_support_pure_iff _ _).mp hret
      subst output
      exact hinv
    | inr q =>
      exact ⟨signingOracleWithAttempts_preserves_attempts sampling.sampleBottom attempt
          (signWithCoins hash family sampling sk) q state hinv.1 output houtput,
        signingOracleWithAttempts_preserves_nodup sampling.sampleBottom attempt
          (signWithCoins hash family sampling sk) q state hinv.1 hinv.2 output houtput⟩
  have hinit : inv (SyncSignatureUnforgeability.emptyHistory, []) := by
    constructor
    · intro entry hentry
      simp at hentry
    · simp
  simp only [runWithKeys, mem_support_bind_iff] at hout
  obtain ⟨pair, hpair, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  exact (OracleComp.simulateQ_run_preservesInv (nativeOracles hash family sampling sk)
    inv hpres (adv.forge pk) (SyncSignatureUnforgeability.emptyHistory, []) hinit pair hpair).2

/-- Native source attempts carry the exact same coin as their full returned signature or failure. -/
theorem runWithKeys_attempts_match_history
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (runWithKeys hash family sampling adv pk sk)) :
    AttemptsMatchHistory sampling.sampleBottom
      (fun ep msg coins => componentResult family sampling.bottom sk (bottomPosition S ep)
        (bottomMessage ep msg) coins)
      (signWithCoins hash family sampling sk) (out.history, out.bottomAttempts) := by
  classical
  let attempt := fun ep msg coins => componentResult family sampling.bottom sk (bottomPosition S ep)
    (bottomMessage ep msg) coins
  let inv :=
    AttemptsMatchHistory sampling.sampleBottom attempt (signWithCoins hash family sampling sk)
  have hpres : QueryImpl.PreservesInv (nativeOracles hash family sampling sk) inv := by
    intro q state hinv output houtput
    cases q with
    | inl uniform =>
      change output ∈ support
        ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at houtput
      obtain ⟨answer, _, hret⟩ := (mem_support_bind_iff _ _ _).mp houtput
      have heq := (mem_support_pure_iff _ _).mp hret
      subst output
      exact hinv
    | inr q =>
      exact signingOracleWithAttempts_preserves_attempts sampling.sampleBottom attempt
        (signWithCoins hash family sampling sk) q state hinv output houtput
  have hinit : inv (SyncSignatureUnforgeability.emptyHistory, []) := by
    intro entry hentry
    simp at hentry
  simp only [runWithKeys, mem_support_bind_iff] at hout
  obtain ⟨pair, hpair, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  exact OracleComp.simulateQ_run_preservesInv (nativeOracles hash family sampling sk)
    inv hpres (adv.forge pk) (SyncSignatureUnforgeability.emptyHistory, []) hinit pair hpair

/-- Every successful native source record has its exact actual bottom-coin witness. -/
theorem runWithKeys_successful_record_signature
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (runWithKeys hash family sampling adv pk sk))
    (ep : Epoch S) (msg : M) (sig : Signature R H S)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ coins ∈ support sampling.sampleBottom,
      signWithCoins hash family sampling sk ep msg coins = some sig := by
  classical
  let inv : NativeState M H R S → Prop := fun state =>
    ReturnedHistory sampling.sampleBottom (signWithCoins hash family sampling sk) state.1
  have hpres : QueryImpl.PreservesInv (nativeOracles hash family sampling sk) inv := by
    intro q state hinv output houtput
    cases q with
    | inl uniform =>
      change output ∈ support
        ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at houtput
      obtain ⟨answer, _, hret⟩ := (mem_support_bind_iff _ _ _).mp houtput
      have heq := (mem_support_pure_iff _ _).mp hret
      subst output
      exact hinv
    | inr q =>
      exact signingOracleWithAttempts_preserves_returns sampling.sampleBottom
        (fun ep msg coins => componentResult family sampling.bottom sk (bottomPosition S ep)
          (bottomMessage ep msg) coins)
        (signWithCoins hash family sampling sk) q state hinv output houtput
  have hinit : inv (SyncSignatureUnforgeability.emptyHistory, []) := by
    intro ep msg sig hentry
    simp [SyncSignatureUnforgeability.emptyHistory] at hentry
  simp only [runWithKeys, mem_support_bind_iff] at hout
  obtain ⟨pair, hpair, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  have hfinal := OracleComp.simulateQ_run_preservesInv
    (nativeOracles hash family sampling sk) inv hpres (adv.forge pk)
    (SyncSignatureUnforgeability.emptyHistory, []) hinit pair hpair
  exact hfinal ep msg sig hrecord

/-- Fixed-key source execution retains exactly its keys and eager certificate metadata. -/
theorem runWithKeys_support_keys
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (runWithKeys hash family sampling adv pk sk)) :
    out.pk = pk ∧ out.sk = sk ∧
      out.upperResults = upperResults hash family sampling.internal sk := by
  classical
  simp only [runWithKeys, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  exact ⟨rfl, rfl, rfl⟩

/-- Every actual source result has its private table computed from that same raw secret key. -/
theorem sourceProgram_upperResults [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv)) :
    out.upperResults = upperResults hash family sampling.internal out.sk := by
  classical
  simp only [sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hrun⟩ := hout
  obtain ⟨_, hsk, hupper⟩ :=
    runWithKeys_support_keys hash family sampling adv pair.1 pair.2 out hrun
  simpa only [hsk] using hupper

/-- A successful source record retains the exact signing callback and an actual bottom coin. -/
theorem sourceProgram_successful_record_signature [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv))
    (ep : Epoch S) (msg : M) (sig : Signature R H S)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ coins ∈ support sampling.sampleBottom,
      signWithCoins hash family sampling out.sk ep msg coins = some sig := by
  classical
  simp only [sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hrun⟩ := hout
  obtain ⟨_, hsk, _⟩ := runWithKeys_support_keys hash family sampling adv pair.1 pair.2 out hrun
  simpa only [hsk] using runWithKeys_successful_record_signature
    hash family sampling adv pair.1 pair.2 out hrun ep msg sig hrecord

/-- Every logged source attempt has its actual coin and complete first-request history answer. -/
theorem sourceProgram_attempts_match_history [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv)) :
    AttemptsMatchHistory sampling.sampleBottom
      (fun ep msg coins => componentResult family sampling.bottom out.sk (bottomPosition S ep)
        (bottomMessage ep msg) coins)
      (signWithCoins hash family sampling out.sk) (out.history, out.bottomAttempts) := by
  classical
  simp only [sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hrun⟩ := hout
  obtain ⟨_, hsk, _⟩ := runWithKeys_support_keys hash family sampling adv pair.1 pair.2 out hrun
  simpa only [hsk] using
    runWithKeys_attempts_match_history hash family sampling adv pair.1 pair.2 out hrun

/-- Actual key generation and adaptive signing retain first-request epoch uniqueness. -/
theorem sourceProgram_bottomAttempts_nodup [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv)) :
    (out.bottomAttempts.map BottomAttempt.epoch).Nodup := by
  classical
  simp only [sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hrun⟩ := hout
  exact runWithKeys_bottomAttempts_nodup hash family sampling adv pair.1 pair.2 out hrun

/-- The public seed in an actual source result is the seed of its retained raw key. -/
theorem sourceProgram_support_seed_eq [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv)) :
    out.pk.seed = out.sk.seed := by
  classical
  simp only [sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨generated, hkeys, hrun⟩ := hout
  obtain ⟨hpk, hsk, _⟩ :=
    runWithKeys_support_keys hash family sampling adv generated.1 generated.2 out hrun
  rw [hpk, hsk]
  simp only [keygen, mem_support_bind_iff] at hkeys
  obtain ⟨pp, _, hstarts⟩ := hkeys
  obtain ⟨starts, _, hcoins⟩ := hstarts
  obtain ⟨coins, _, hret⟩ := hcoins
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst generated
  rfl

/-- Erase raw upper coins while retaining the complete seed, start and endpoint material. -/
@[expose] def eraseUpperCoins (sk : SecretKey PP H Coins S) : SecretKey PP H Unit S :=
  ⟨sk.seed, sk.starts, sk.endpoints, fun _ => ()⟩

/-- Materialize a signature from selected encoding results and coin-free key material. -/
@[expose] def signFromResults (hash : HashInstance PP T X H S) (sk : SecretKey PP H Unit S)
    (upper : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) (ep : Epoch S)
    (bottom : Option (Codeword S.v (2 ^ S.w) × R)) : Option (Signature R H S) := do
  let wr ← bottom
  let uppers ← Fin.mOfFn (S.d - 1) fun i =>
    (upper (upperPositionAt S ep i)).map
      (componentSignature hash sk (upperPositionAt S ep i).1)
  pure ⟨componentSignature hash sk (bottomPosition S ep) wr, uppers⟩

/-- Honest signing observes upper coins only through their fixed optional certificate results. -/
theorem signWithCoins_eq_signFromResults (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) :
    signWithCoins hash family sampling sk ep msg coins =
      signFromResults hash (eraseUpperCoins sk)
        (fun p => (upperResults hash family sampling.internal sk p).output) ep
        (componentResult family sampling.bottom sk (bottomPosition S ep)
          (bottomMessage ep msg) coins).output := rfl

/-- One certificate's complete retry result as a function of only its own coin value. -/
@[expose] def upperResultAt (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (p : UpperPosition S) (coin : plan.Coins) :
    IncomparableEncoding.IndexedResult R S.v (2 ^ S.w) :=
  componentResult family plan (keys hash pp starts (fun _ => ())).2 p.1
    (internalMessage p (componentRoot hash pp (endpoints hash pp starts) (childTree S p))) coin

/-- The actual fixed-tape table is coordinatewise evaluation of the stored tapes. -/
theorem upperResults_keys (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (coins : UpperPosition S → plan.Coins) :
    upperResults hash family plan (keys hash pp starts coins).2 =
      fun p => upperResultAt hash family plan pp starts p (coins p) := rfl

/-- Independently sampled complete results, retaining all upper retry metadata. -/
noncomputable def sampleUpperResults (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (sample : ProbComp plan.Coins) :
    ProbComp (UpperResults R S) := by
  letI : Fintype (UpperPosition S) := Fintype.ofFinite _
  exact Fintype.mPi fun p => (upperResultAt hash family plan pp starts p) <$> sample

/-- The joint fixed-tape-to-result sampling law is an equality of the actual local computations.
It forgets raw coins and retains full results, rather than asserting equality of secret keys. -/
theorem map_sampleUpperCoins_eq_sampleUpperResults (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (sample : ProbComp plan.Coins) :
    (fun coins => upperResults hash family plan (keys hash pp starts coins).2) <$>
        sampleUpperCoins S sample =
      sampleUpperResults hash family plan pp starts sample := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  unfold sampleUpperCoins sampleUpperResults
  rw [← Fintype.mPi_map]
  rfl

/-- Optional result projection commutes with the actual independent upper-result sampler. -/
theorem map_output_sampleUpperResults (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (sample : ProbComp plan.Coins) :
    (fun results : UpperResults R S => fun p => (results p).output) <$>
        sampleUpperResults hash family plan pp starts sample =
      (by
        letI : Fintype (UpperPosition S) := Fintype.ofFinite _
        exact Fintype.mPi fun p : UpperPosition S =>
          (fun coin => (upperResultAt hash family plan pp starts p coin).output) <$> sample) := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  unfold sampleUpperResults
  rw [Fintype.mPi_map]
  simp only [Functor.map_map]

/-- The key observation needed by encoding simulation erases raw coins and retains full results. -/
@[expose] def keyObservation (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (generated : GXMSS.PublicKey PP H × SecretKey PP H sampling.internal.Coins S) :
    GXMSS.PublicKey PP H × SecretKey PP H Unit S × UpperResults R S :=
  (generated.1, eraseUpperCoins generated.2,
    upperResults hash family sampling.internal generated.2)

/-- Key material with independently sampled full certificate results and erased raw tapes. -/
noncomputable def keygenFromResults [SampleableType H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) :
    ProbComp (GXMSS.PublicKey PP H × SecretKey PP H Unit S × UpperResults R S) := do
  let pp ← hash.thf.seedGen
  let starts ← sampleStarts S
  let results ← sampleUpperResults hash family sampling.internal pp starts sampling.sampleInternal
  let generated := keys hash pp starts (fun _ => ())
  pure (generated.1, generated.2, results)

/-- The actual joint key-generation observation is the local full-result sampling construction.
No equality of raw secret keys or conditioning on successful certificates is asserted. -/
theorem keygen_map_keyObservation [SampleableType H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) :
    keyObservation hash family sampling <$> keygen hash sampling =
      keygenFromResults hash family sampling := by
  unfold keygen keygenFromResults
  simp only [map_bind, map_pure]
  apply bind_congr
  intro pp
  apply bind_congr
  intro starts
  rw [← map_sampleUpperCoins_eq_sampleUpperResults]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

/-- A fixed finite order containing every internal coordinate exactly once. -/
@[expose] noncomputable def upperOrder (S : Shape) : List (UpperPosition S) := by
  letI : Fintype (UpperPosition S) := Fintype.ofFinite _
  exact List.ofFn (Fintype.equivFin (UpperPosition S)).symm

/-- The eager ledger has the full upper-certificate cardinality, including failed coordinates. -/
theorem upperOrder_length (S : Shape) : (upperOrder S).length = upperCount S := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  simp only [upperOrder, List.length_ofFn]
  exact (Nat.card_eq_fintype_card).symm.trans (card_upperPosition S)

/-- Observe each full private result as an encoding-game record, preserving returned exhaustion. -/
@[expose] noncomputable def upperLedger (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S) : FamilyEncoding.Transcript M H R S :=
  (upperOrder S).map fun p =>
    ⟨p.1, internalMessage p (componentRoot hash sk.seed sk.endpoints (childTree S p)),
      (upperResults hash family plan sk p).output⟩

/-- The optional upper ledger records exactly one entry per internal coordinate. -/
theorem upperLedger_length (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S) :
    (upperLedger hash family plan sk).length = upperCount S := by
  simp [upperLedger, upperOrder_length]

/-- Observe the full bottom attempt log as family-game records, preserving every failed request. -/
@[expose] def bottomLedger (attempts : List (BottomAttempt M R S)) :
    FamilyEncoding.Transcript M H R S :=
  attempts.map fun entry =>
    ⟨bottomPosition S entry.epoch, bottomMessage entry.epoch entry.message, entry.result.output⟩

/-- Optional observation forgets metadata without dropping any consumed bottom request. -/
@[simp] theorem bottomLedger_length (attempts : List (BottomAttempt M R S)) :
    (bottomLedger (H := H) attempts).length = attempts.length := by simp [bottomLedger]

/-- Observe a fixed optional upper-result table as all internal family-game records. -/
@[expose] noncomputable def upperLedgerFromResults (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Coins S)
    (results : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) :
    FamilyEncoding.Transcript M H R S :=
  (upperOrder S).map fun p =>
    ⟨p.1, internalMessage p (componentRoot hash sk.seed sk.endpoints (childTree S p)), results p⟩

/-- The full private encoding ledger counts every internal certificate and eligible bottom call. -/
@[expose] noncomputable def encodingLedger (hash : HashInstance PP T X H S)
    (out : Result PP H M R Coins S) : FamilyEncoding.Transcript M H R S :=
  upperLedgerFromResults hash out.sk (fun p => (out.upperResults p).output) ++
    bottomLedger out.bottomAttempts

/-- Every internal coordinate occurs in the fixed eager enumeration. -/
theorem mem_upperOrder (S : Shape) (p : UpperPosition S) : p ∈ upperOrder S := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  exact List.mem_ofFn.mpr ⟨(Fintype.equivFin (UpperPosition S)) p, by simp⟩

/-- The optional upper table retains exactly all upper coordinates, including failed results. -/
@[simp] theorem upperLedgerFromResults_length (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Coins S)
    (results : UpperPosition S → Option (Codeword S.v (2 ^ S.w) × R)) :
    (upperLedgerFromResults (M := M) hash sk results).length = upperCount S := by
  simp [upperLedgerFromResults, upperOrder_length]

/-- The exact consumed encoding reference at a complete coordinate. Upper coordinates always
have a private record; bottom coordinates have one exactly when a first request reached them. -/
@[expose] def referenceAt (hash : HashInstance PP T X H S)
    (out : Result PP H M R Coins S) (p : OTSPosition S) :
    Option (FamilyEncoding.Record M H R S) :=
  if hp : p.1.1.val = 0 then
    (bottomLedger out.bottomAttempts).find? fun entry => decide (entry.position = p)
  else
    let upper : UpperPosition S := ⟨p, hp⟩
    some ⟨p, internalMessage upper
      (componentRoot hash out.sk.seed out.sk.endpoints (childTree S upper)),
      (out.upperResults upper).output⟩

/-- A returned encoding reference belongs to the exact coordinate at which it was requested. -/
theorem referenceAt_position (hash : HashInstance PP T X H S)
    (out : Result PP H M R Coins S) (p : OTSPosition S)
    (entry : FamilyEncoding.Record M H R S) (h : referenceAt hash out p = some entry) :
    entry.position = p := by
  unfold referenceAt at h
  split_ifs at h with hp
  · have hp' : decide (entry.position = p) = true :=
      List.find?_some (p := fun entry : FamilyEncoding.Record M H R S =>
        decide (entry.position = p)) h
    exact of_decide_eq_true hp'
  · have heq := Option.some.inj h
    exact congrArg FamilyEncoding.Record.position heq.symm

/-- A bottom reference comes from an actual private first-request attempt, with its exact message
and optional selected result preserved. -/
theorem referenceAt_bottom_attempt (hash : HashInstance PP T X H S)
    (out : Result PP H M R Coins S) (p : OTSPosition S) (hp : p.1.1.val = 0)
    (entry : FamilyEncoding.Record M H R S) (h : referenceAt hash out p = some entry) :
    ∃ attempt ∈ out.bottomAttempts, bottomPosition S attempt.epoch = p ∧
      entry = (⟨bottomPosition S attempt.epoch, bottomMessage attempt.epoch attempt.message,
        attempt.result.output⟩ : FamilyEncoding.Record M H R S) := by
  have hposition := referenceAt_position hash out p entry h
  unfold referenceAt at h
  rw [dite_eq_left hp] at h
  have hmem := List.mem_of_find?_eq_some h
  obtain ⟨attempt, hattempt, heq⟩ := List.mem_map.mp hmem
  exact ⟨attempt, hattempt, (congrArg FamilyEncoding.Record.position heq).trans hposition,
    heq.symm⟩

/-- The bottom-coordinate query representation preserves the application message exactly. -/
theorem bottomQuery_message_eq (ep : Epoch S) (msg msg' : M)
    (h : (⟨bottomPosition S ep, bottomMessage ep msg⟩ : FamilyEncoding.Query M H S) =
      ⟨bottomPosition S ep, bottomMessage ep msg'⟩) : msg = msg' := by
  have hmsg := (Sigma.mk.inj_iff.mp h).2
  exact eq_of_heq hmsg

/-- A successful bottom reference with matching query and successful fixed upper certificates
is the exact full signature returned in the actual synchronized history. -/
theorem history_of_referenceAt_bottom_success [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv))
    (ep : Epoch S) (msg : M) (entry : FamilyEncoding.Record M H R S)
    (wr : Codeword S.v (2 ^ S.w) × R)
    (upper : Fin (S.d - 1) → GXMSS.Signature R H S.h S.v)
    (href : referenceAt hash out (bottomPosition S ep) = some entry)
    (hresult : entry.result = some wr)
    (hquery : (⟨entry.position, entry.message⟩ : FamilyEncoding.Query M H S) =
      ⟨bottomPosition S ep, bottomMessage ep msg⟩)
    (hupper : ∀ i, certificate hash family sampling.internal out.sk (upperPositionAt S ep i) =
      some (upper i)) :
    out.history ep = some (msg,
      some (⟨componentSignature hash out.sk (bottomPosition S ep) wr, upper⟩ :
        Signature R H S)) := by
  classical
  obtain ⟨attempt, hattempt, hposition, hentry⟩ :=
    referenceAt_bottom_attempt hash out (bottomPosition S ep) rfl entry href
  have hepoch : attempt.epoch = ep := positionAt_bottom_injective S hposition
  subst entry
  change (⟨bottomPosition S attempt.epoch, bottomMessage attempt.epoch attempt.message⟩ :
    FamilyEncoding.Query M H S) = ⟨bottomPosition S ep, bottomMessage ep msg⟩ at hquery
  rw [hepoch] at hquery
  have hmessage : attempt.message = msg := bottomQuery_message_eq ep attempt.message msg hquery
  obtain ⟨coins, _, hactual, hhistory⟩ :=
    sourceProgram_attempts_match_history hash family sampling adv out hout attempt hattempt
  have hbottom : (componentResult family sampling.bottom out.sk (bottomPosition S ep)
      (bottomMessage ep msg) coins).output = some wr := by
    change attempt.result.output = some wr at hresult
    rw [hactual] at hresult
    rw [hepoch, hmessage] at hresult
    exact hresult
  have hfull : signWithCoins hash family sampling out.sk ep msg coins =
      some (⟨componentSignature hash out.sk (bottomPosition S ep) wr, upper⟩ :
        Signature R H S) := by
    have hupper' := (fin_mOfFn_eq_some_iff
      (fun i => certificate hash family sampling.internal out.sk (upperPositionAt S ep i))
      upper).mpr
        hupper
    simp [signWithCoins, hbottom, hupper']
  simpa only [hepoch, hmessage, hfull] using hhistory

/-- Every successful actual source reference re-encodes in its own coordinate and message fibre. -/
theorem referenceAt_value_eq_some [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S)
    (out : Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (sourceProgram hash family sampling adv))
    (p : OTSPosition S) (entry : FamilyEncoding.Record M H R S)
    (href : referenceAt hash out p = some entry)
    (word : Codeword S.v (2 ^ S.w)) (r : R) (hresult : entry.result = some (word, r)) :
    family.value entry.position out.sk.seed entry.message r = some word := by
  classical
  by_cases hp : p.1.1.val = 0
  · obtain ⟨attempt, hattempt, _, hentry⟩ :=
      referenceAt_bottom_attempt hash out p hp entry href
    subst entry
    obtain ⟨coins, _, hactual, _⟩ :=
      sourceProgram_attempts_match_history hash family sampling adv out hout attempt hattempt
    change attempt.result.output = some (word, r) at hresult
    rw [hactual] at hresult
    dsimp only at hresult
    rw [componentResult_eq_run] at hresult
    exact sampling.bottom.value_eq_some_of_run_output_eq_some _ _ _ _ coins hresult
  · unfold referenceAt at href
    rw [dite_eq_right hp] at href
    have heq := Option.some.inj href
    subst entry
    change (out.upperResults ⟨p, hp⟩).output = some (word, r) at hresult
    rw [sourceProgram_upperResults hash family sampling adv out hout] at hresult
    change (componentResult family sampling.internal out.sk p
      (internalMessage ⟨p, hp⟩
        (componentRoot hash out.sk.seed out.sk.endpoints (childTree S ⟨p, hp⟩)))
      (out.sk.upperCoins ⟨p, hp⟩)).output = some (word, r) at hresult
    rw [componentResult_eq_run] at hresult
    exact sampling.internal.value_eq_some_of_run_output_eq_some _ _ _ _ _ hresult

/-- Every returned reference is present in the full private encoding ledger. -/
theorem referenceAt_mem_encodingLedger (hash : HashInstance PP T X H S)
    (out : Result PP H M R Coins S) (p : OTSPosition S)
    (entry : FamilyEncoding.Record M H R S) (h : referenceAt hash out p = some entry) :
    entry ∈ encodingLedger hash out := by
  unfold referenceAt at h
  split_ifs at h with hp
  · exact List.mem_append_right _ (List.mem_of_find?_eq_some h)
  · have heq := Option.some.inj h
    subst entry
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨⟨p, hp⟩, mem_upperOrder S ⟨p, hp⟩, rfl⟩

/-- Materialize the reference signature only from its selected encoding result and actual starts. -/
@[expose] def referenceSignatureAt (hash : HashInstance PP T X H S)
    (out : Result PP H M R Coins S) (p : OTSPosition S) :
    Option (GXMSS.Signature R H S.h S.v) :=
  (referenceAt hash out p).bind fun entry => entry.result.map (componentSignature hash out.sk p)

end GXMSS.Hypertree.Security
