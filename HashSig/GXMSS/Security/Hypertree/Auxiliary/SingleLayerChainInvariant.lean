/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainMass
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Reachable spliced first-request ledgers

Surviving filtered signing interactions retain the actual full bottom-attempt result and its
sampled coin, every consumed history entry has an attempt, and logged epochs remain distinct.
These statements apply to arbitrary shapes and retry samplers, including failed signatures.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec
open _root_.GXMSS.Hypertree.Security

variable {PP T X H M R Coins : Type} {S : Shape}

/-- Full attempt/history association, history coverage and distinct consumed epochs. -/
@[expose] def AttemptHistoryInvariant (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S))
    (state : NativeState M H R S) : Prop :=
  AttemptsMatchHistory sample attempt signer state ∧ HistoryHasAttempt state ∧
    (state.2.map BottomAttempt.epoch).Nodup

/-- The explicit-coin signing handler preserves all three first-request ledger properties. -/
theorem oraclesWithAttempts_preserves_attemptHistoryInvariant (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S)) :
    QueryImpl.PreservesInv (ChainMass.oraclesWithAttempts sample attempt signer)
      (AttemptHistoryInvariant sample attempt signer) := by
  intro q state hinv out hout
  cases q with
  | inl uniform =>
    change out ∈ support ((fun answer => (answer, state)) <$>
      (unifSpec.query uniform : ProbComp _)) at hout
    obtain ⟨_, _, heq⟩ := OracleComp.mem_support_map_peel _ _ hout
    cases heq
    exact hinv
  | inr request =>
    exact ⟨signingOracleWithAttempts_preserves_attempts sample attempt signer request state
        hinv.1 out hout,
      signingOracleWithAttempts_preserves_historyHasAttempt sample attempt signer request state
        hinv.2.1 out hout,
      signingOracleWithAttempts_preserves_nodup sample attempt signer request state hinv.1
        hinv.2.2 out hout⟩

/-- An absorbing optional-state filter preserves any invariant on its surviving native states. -/
theorem filteredOracles_preserves_survivingInvariant
    (original : QueryImpl (ChainMass.FullSpec M H R S) (StateT (NativeState M H R S) ProbComp))
    (bad : NativeState M H R S → Bool) (inv : NativeState M H R S → Prop)
    (hpres : QueryImpl.PreservesInv original inv) :
    QueryImpl.PreservesInv (ChainMass.filteredOracles original bad)
      (fun state => state.elim True inv) := by
  intro q state hinv out hout
  cases state with
  | none =>
    change out ∈ support (pure (ChainMass.dummy q, none) : ProbComp _) at hout
    have heq := (mem_support_pure_iff _ _).mp hout
    subst out
    trivial
  | some state =>
    change out ∈ support ((fun result =>
      (if bad result.2 then ChainMass.dummy q else result.1,
        if bad result.2 then none else some result.2)) <$> (original q).run state) at hout
    obtain ⟨result, hresult, heq⟩ := OracleComp.mem_support_map_peel _ _ hout
    cases heq
    have hnext := hpres q state hinv result hresult
    split_ifs
    · trivial
    · exact hnext

/-- The reachable ledger invariant for the actual spliced signing callback. -/
@[expose] def SpliceStateInvariant (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (state : NativeState M H R S) : Prop :=
  AttemptHistoryInvariant sampling.sampleBottom
    (ChainContinuation.bottomResult family sampling.bottom pp)
    (ChainContinuation.spliceSign hash family sampling pp selected i cut answer starts upperCoins)
    state

/-- Actual spliced oracle steps preserve the complete first-request ledger invariant. -/
theorem spliceOracles_preserves_invariant (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) :
    QueryImpl.PreservesInv
      (ChainMass.spliceOracles hash family sampling pp selected i cut answer starts upperCoins)
      (SpliceStateInvariant hash family sampling pp selected i cut answer starts upperCoins) :=
  oraclesWithAttempts_preserves_attemptHistoryInvariant sampling.sampleBottom
    (ChainContinuation.bottomResult family sampling.bottom pp)
    (ChainContinuation.spliceSign hash family sampling pp selected i cut answer starts upperCoins)

/-- The absorbing selected-read filter preserves the invariant on every surviving native state. -/
theorem filteredSpliceOracles_preserves_invariant (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (threshold cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) :
    QueryImpl.PreservesInv
      (ChainMass.filteredSpliceOracles hash family sampling pp selected i threshold cut answer
        starts upperCoins)
      (fun state => state.elim True
        (SpliceStateInvariant hash family sampling pp selected i cut answer starts upperCoins)) :=
  filteredOracles_preserves_survivingInvariant _ _ _
    (spliceOracles_preserves_invariant hash family sampling pp selected i cut answer starts
      upperCoins)

/-- Every surviving output of the actual filtered adaptive interaction has an actual coin-backed
attempt for each consumed request, exact history association and no repeated logged epoch. -/
theorem runFilteredRaw_surviving_invariant (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (adv : SchemeAdversary PP H M R S) (pp : PP) (selected : OTSPosition S) (i : Fin S.v)
    (threshold cut : ℕ) (answer : H) (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (out : SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S) ×
      Option (NativeState M H R S))
    (hout : out ∈ support (ChainMass.runFilteredRaw hash family sampling adv pp selected i
      threshold cut answer starts upperCoins))
    (state : NativeState M H R S) (hstate : out.2 = some state) :
    SpliceStateInvariant hash family sampling pp selected i cut answer starts upperCoins state := by
  let inv := SpliceStateInvariant hash family sampling pp selected i cut answer starts upperCoins
  have hinit : inv (SyncSignatureUnforgeability.emptyHistory, []) := by
    refine ⟨?_, ?_, ?_⟩
    · intro entry hentry
      simp at hentry
    · intro ep msg response hrecord
      simp [SyncSignatureUnforgeability.emptyHistory] at hrecord
    · simp
  have hpres := filteredSpliceOracles_preserves_invariant hash family sampling pp selected i
    threshold cut answer starts upperCoins
  unfold ChainMass.runFilteredRaw at hout
  have hresult := OracleComp.simulateQ_run_preservesInv _
    (fun state : Option (NativeState M H R S) => state.elim True inv) hpres _ _
    (by split_ifs <;> trivial) out hout
  simpa only [hstate, Option.elim_some] using hresult

end GXMSS.Hypertree.SingleLayer
