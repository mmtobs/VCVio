/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainContinuation
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
public import HashSig.GXMSS.Security.Auxiliary.FilteredSimulation
public import HashSig.GXMSS.Security.Auxiliary.ReturnedMass
public import HashSig.GXMSS.Security.Auxiliary.HybridTelescope
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
import all VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.OracleComp.OracleSpec

/-!
# Global chain selector and disclosed-prefix filters

The selector ranges over all forest chain positions once. Disclosed-read rejection observes
only complete returned signatures; full bottom retry records remain in the private native
ledger even when a later fixed certificate fails. Private upper retry results are retained
separately. Selected-event completeness is an explicit deterministic proof obligation.
-/

public section

namespace GXMSS.Hypertree.Security.ChainMass

open Encoding ENNReal OracleComp OracleSpec TweakableHash
open ChainContinuation

variable {PP T X H M R : Type} {S : Shape}

/-- A concrete uniform sampler for the complete finite chain-position domain. -/
@[reducible] noncomputable def selectorSampling (S : Shape) (hv : 0 < S.v) (hw : 0 < S.w) :
    SampleableType (ChainPosition S) := by
  let : Fintype (ChainPosition S) := Fintype.ofFinite _
  have hn : 0 < 2 ^ S.w - 1 := by
    have := Nat.one_lt_two_pow (Nat.ne_of_gt hw)
    omega
  let : Nonempty (ChainPosition S) :=
    ⟨((topTree S, ⟨0, S.branching_pos⟩), ⟨0, hv⟩, ⟨0, hn⟩)⟩
  exact SampleableType.ofFintype _

/-- Draw one global coordinate without an additional component selector. -/
@[expose] noncomputable def sampleSelector (S : Shape) (hv : 0 < S.v) (hw : 0 < S.w) :
    ProbComp (ChainPosition S) := by
  let : SampleableType (ChainPosition S) := selectorSampling S hv hw
  exact $ᵗ (ChainPosition S)

/-- The uniform selector has precisely the full forest positive-chain cardinality. -/
theorem selector_cardinality (S : Shape) : Nat.card (ChainPosition S) = chainCount S :=
  card_chainPosition S

/-- A supplied deterministic component witness designates one global chain selector. -/
@[expose] def selectedObservation {A : Type} (win : A → Bool)
    (choose : A → Option (ChainPosition S)) (guess : ChainPosition S) (out : A) : Bool :=
  win out && decide (choose out = some guess)

/-- One complete deterministic selected witness has exactly inverse global-cardinality mass. -/
theorem selected_probability {A : Type} (hv : 0 < S.v) (hw : 0 < S.w)
    (win : A → Bool) (choose : A → Option (ChainPosition S)) (out : A)
    (hcomplete : win out = true → (choose out).isSome = true) :
    Pr{let guess ← sampleSelector S hv hw}[selectedObservation win choose guess out = true] =
      if win out = true then (chainCount S : ℝ≥0∞)⁻¹ else 0 := by
  let : Fintype (ChainPosition S) := Fintype.ofFinite _
  let : SampleableType (ChainPosition S) := selectorSampling S hv hw
  have hcard : Fintype.card (ChainPosition S) = chainCount S :=
    Nat.card_eq_fintype_card.symm.trans (card_chainPosition S)
  rw [← hcard]
  apply GXMSS.Reductions.ReturnedMass.uniform_selector_probability
  · intro hwin
    cases hout : choose out with
    | none => exact False.elim (by simpa [hout] using hcomplete hwin)
    | some target =>
        exact ⟨target, fun guess => by simp [selectedObservation, hwin, hout, eq_comm]⟩
  · intro guess hguess
    exact (Bool.and_eq_true_iff.mp hguess).1

/-- Actual source execution with a single independent global selector sampled before interaction. -/
noncomputable def selectedSource [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (win : Result PP H M R sampling.internal.Coins S → Bool)
    (choose : Result PP H M R sampling.internal.Coins S → Option (ChainPosition S)) :
    ProbComp Bool := do
  let guess ← sampleSelector S hv hw
  let out ← sourceProgram hash family sampling adv
  pure (selectedObservation win choose guess out)

/-- Exact global-selector accounting on the actual source program. Coverage must be proved
for the chosen deterministic witness; it is not supplied by this probability identity. -/
theorem selectedSource_mass [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (win : Result PP H M R sampling.internal.Coins S → Bool)
    (choose : Result PP H M R sampling.internal.Coins S → Option (ChainPosition S))
    (hcomplete : ∀ out ∈ support (sourceProgram hash family sampling adv),
      win out = true → (choose out).isSome = true) :
    let : MeasurableSpace (Result PP H M R sampling.internal.Coins S) := ⊤
    𝒟[selectedSource hash family sampling hv hw adv win choose] {true} =
      (chainCount S : ℝ≥0∞)⁻¹ *
        𝒟[sourceProgram hash family sampling adv] {out | win out = true} := by
  let : MeasurableSpace (Result PP H M R sampling.internal.Coins S) := ⊤
  have hswap : 𝒟[selectedSource hash family sampling hv hw adv win choose] =
      𝒟[do
        let out ← sourceProgram hash family sampling adv
        let guess ← sampleSelector S hv hw
        pure (selectedObservation win choose guess out)] := by
    unfold selectedSource
    exact OracleComp.evalDist_bind_bind_swap _ _ _
  rw [hswap]
  apply GXMSS.Reductions.ReturnedMass.bind_true_mass_eq_mul_event
  intro out hout
  have hp := selected_probability hv hw win choose out (hcomplete out hout)
  have hobs :
      Pr{let guess ← sampleSelector S hv hw}[selectedObservation win choose guess out = true] =
      𝒟[(fun guess => selectedObservation win choose guess out) <$> sampleSelector S hv hw]
        {true} :=
    (prEvent_map _ (fun guess => selectedObservation win choose guess out)
      (fun b => b = true)).symm.trans (prEvent_eq_evalDist_singleton _ true)
  rw [hobs] at hp
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using hp

/-- A complete returned word tuple reveals a low prefix at the selected global chain. -/
@[expose] def disclosedBad (metadata : Metadata R H S) (selected : OTSPosition S)
    (i : Fin S.v) (threshold : ℕ) (attempt : BottomAttempt M R S) : Bool :=
  (wordsFromResult metadata attempt.epoch attempt.result).elim false fun words =>
    decide ((bottomPosition S attempt.epoch = selected ∧ (words.1.1 i).val < threshold) ∨
      ∃ k : Fin (S.d - 1), (upperPositionAt S attempt.epoch k).1 = selected ∧
        ((words.2 k).1 i).val < threshold)

/-- A selected private upper certificate may also be used by the eventual witness. -/
@[expose] def privateBad (metadata : Metadata R H S) (selected : OTSPosition S)
    (i : Fin S.v) (threshold : ℕ) : Bool :=
  if h : selected.1.1.val = 0 then false else
    (metadata.internalResults ⟨selected, h⟩).output.elim false fun wr =>
      decide ((wr.1 i).val < threshold)

/-- A good private upper result bounds the selected digit of its canonical reference. -/
theorem privateBad_false_word_ge (metadata : Metadata R H S) (selected : OTSPosition S)
    (i : Fin S.v) (threshold : ℕ) (p : UpperPosition S)
    (wr : Codeword S.v (2 ^ S.w) × R) (hp : p.val = selected)
    (hword : (metadata.internalResults p).output = some wr)
    (hbad : privateBad metadata selected i threshold = false) :
    threshold ≤ (wr.1 i).val := by
  subst selected
  have hnot : ¬(wr.1 i).val < threshold := by
    simpa only [privateBad, p.property, ↓reduceDIte, hword, Option.elim_some,
      decide_eq_false_iff_not] using hbad
  exact Nat.le_of_not_gt hnot

/-- Canonical private reference signatures also agree across adjacent surviving cuts. -/
theorem canonicalReferences_advance (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (threshold cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) (coins : UpperPosition S → plan.Coins)
    (hn : cut + 2 ≤ 2 ^ S.w - 1) (hthreshold : cut + 2 ≤ threshold)
    (hbad : privateBad (prepare hash family plan pp
      (spliceEndpoints hash pp selected i cut answer starts) coins) selected i threshold = false) :
    canonicalReferences (prepare hash family plan pp
        (spliceEndpoints hash pp selected i cut answer starts) coins)
      (splicePrefixes hash pp selected i cut answer starts) =
    canonicalReferences (prepare hash family plan pp
        (spliceEndpoints hash pp selected i (cut + 1)
          ((chainFamily hash pp).chain selected i (cut + 1) 1 answer) starts) coins)
      (splicePrefixes hash pp selected i (cut + 1)
        ((chainFamily hash pp).chain selected i (cut + 1) 1 answer) starts) := by
  rw [← prepare_advance hash family plan pp selected i cut answer starts coins hn]
  funext p
  unfold canonicalReferences
  cases hword : ((prepare hash family plan pp
      (spliceEndpoints hash pp selected i cut answer starts) coins).internalResults p).output with
  | none => rfl
  | some wr =>
      simp only [Option.map_some]
      apply congrArg some
      apply component_eq_of_prefix_eq
      intro j
      apply GXMSS.Reductions.ChainContinuation.spliceValue_advance
      intro hp hj
      have hge := privateBad_false_word_ge _ selected i threshold p wr hp hword hbad
      simpa only [hj] using hthreshold.trans hge

/-- Safe canonical references at zero cut are independent of the hidden old start. -/
theorem canonicalReferences_zero_start_update (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) (replacement : H)
    (coins : UpperPosition S → plan.Coins) (hn : 0 < 2 ^ S.w - 1)
    (hthreshold : 0 < threshold)
    (hbad : privateBad (prepare hash family plan pp
      (spliceEndpoints hash pp selected i 0 answer starts) coins) selected i threshold = false) :
    canonicalReferences (prepare hash family plan pp (spliceEndpoints hash pp selected i 0 answer
        (Function.update starts selected (Function.update (starts selected) i replacement))) coins)
      (splicePrefixes hash pp selected i 0 answer
        (Function.update starts selected (Function.update (starts selected) i replacement))) =
    canonicalReferences (prepare hash family plan pp
        (spliceEndpoints hash pp selected i 0 answer starts) coins)
      (splicePrefixes hash pp selected i 0 answer starts) := by
  rw [prepare_zero_start_update hash family plan pp selected i answer starts replacement coins hn]
  funext p
  unfold canonicalReferences
  cases hword : ((prepare hash family plan pp
      (spliceEndpoints hash pp selected i 0 answer starts) coins).internalResults p).output with
  | none => rfl
  | some wr =>
      simp only [Option.map_some]
      apply congrArg some
      apply component_eq_of_prefix_eq
      intro j
      apply GXMSS.Reductions.ChainContinuation.spliceValue_zero_start_update
      intro hp hj
      have hge := privateBad_false_word_ge _ selected i threshold p wr hp hword hbad
      simpa only [hj] using hthreshold.trans_le hge

/-- Rejection is absorbing in the native first-request ledger. Failed full signatures contribute
their full private bottom result but do not contribute disclosed prefix reads. -/
@[expose] def badState (metadata : Metadata R H S) (selected : OTSPosition S)
    (i : Fin S.v) (threshold : ℕ) (state : NativeState M H R S) : Bool :=
  privateBad metadata selected i threshold ||
    state.2.any (disclosedBad metadata selected i threshold)

/-- If the newly extended ledger is good, its current full returned word tuple is safe. -/
theorem disclosedBad_eq_false_of_append (metadata : Metadata R H S)
    (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ)
    (history : SyncSignatureUnforgeability.History (Epoch S) M (Signature R H S))
    (attempts : List (BottomAttempt M R S)) (attempt : BottomAttempt M R S)
    (h : badState metadata selected i threshold (history, attempts ++ [attempt]) = false) :
    disclosedBad metadata selected i threshold attempt = false := by
  simp only [badState, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_false_iff] at h
  exact h.2.2

/-- A good full-return disclosure guard supplies every selected-chain read bound. -/
theorem reads_safe_of_disclosedBad_eq_false (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (pp : PP) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) (metadata : Metadata R H S)
    (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ)
    (hbad : disclosedBad metadata selected i threshold
      ⟨ep, msg, bottomResult family sampling.bottom pp ep msg coins⟩ = false)
    (p : OTSPosition S) (j : Fin S.v) (position : ℕ)
    (hread : Reads family sampling pp ep msg coins metadata p j position)
    (hp : p = selected) (hj : j = i) : threshold ≤ position := by
  cases hw : wordResults family sampling pp ep msg coins metadata with
  | none =>
      have hsuccess := hread.1
      simp [FullSuccess, hw] at hsuccess
  | some words =>
      change wordsFromResult metadata ep (bottomResult family sampling.bottom pp ep msg coins) =
        some words at hw
      have hparts := wordsFromResult_success metadata ep
        (bottomResult family sampling.bottom pp ep msg coins) words hw
      have hnot : ¬((bottomPosition S ep = selected ∧ (words.1.1 i).val < threshold) ∨
          ∃ k : Fin (S.d - 1), (upperPositionAt S ep k).1 = selected ∧
            ((words.2 k).1 i).val < threshold) := by
        simpa only [disclosedBad, hw, Option.elim_some, decide_eq_false_iff_not] using hbad
      rcases hread.2 with ⟨hposition, wr, hword, hdigit⟩ |
        ⟨k, hposition, wr, hword, hdigit⟩
      · have heq : wr = words.1 := Option.some.inj (hword.symm.trans hparts.1)
        subst wr
        have hd : position = (words.1.1 i).val := by simpa only [hj] using hdigit
        have hn : ¬(words.1.1 i).val < threshold :=
          fun hlt => hnot (Or.inl ⟨hposition.symm.trans hp, hlt⟩)
        omega
      · have heq : wr = words.2 k := Option.some.inj (hword.symm.trans (hparts.2 k))
        subst wr
        have hd : position = ((words.2 k).1 i).val := by simpa only [hj] using hdigit
        have hn : ¬((words.2 k).1 i).val < threshold :=
          fun hlt => hnot (Or.inr ⟨k, hposition.symm.trans hp, hlt⟩)
        omega

/-- The full ambient-randomness and global-signing interface. -/
abbrev FullSpec (M H R : Type) (S : Shape) :=
  unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M (Signature R H S)

/-- A typed killed-branch response. It is used only after the absorbing rejection state. -/
@[expose] def dummy (q : (FullSpec M H R S).Domain) : (FullSpec M H R S).Range q :=
  match q with
  | .inl n => (0 : Fin (n + 1))
  | .inr _ => none

/-- The actual native ledger handler with supplied explicit-coin attempt and signature callbacks. -/
@[expose] def oraclesWithAttempts {Coins : Type} (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S)) :
    QueryImpl (FullSpec M H R S) (StateT (NativeState M H R S) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (NativeState M H R S) ProbComp) + signingOracleWithAttempts sample attempt signer

/-- Absorb rejection while preserving the full native ledger on every surviving query. -/
@[expose] def filteredOracles
    (original : QueryImpl (FullSpec M H R S) (StateT (NativeState M H R S) ProbComp))
    (bad : NativeState M H R S → Bool) :
    QueryImpl (FullSpec M H R S) (StateT (Option (NativeState M H R S)) ProbComp) :=
  fun q state => match state with
  | none => pure (dummy q, none)
  | some state => (fun out =>
      (if bad out.2 then dummy q else out.1, if bad out.2 then none else some out.2)) <$>
        (original q).run state

/-- A previously bad native state stays bad: consumed requests never remove private attempts. -/
theorem badState_mono {Coins : Type} (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S)) (metadata : Metadata R H S)
    (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ)
    (q : (FullSpec M H R S).Domain) (state : NativeState M H R S)
    (hbad : badState metadata selected i threshold state = true)
    (out : (FullSpec M H R S).Range q × NativeState M H R S)
    (hout : out ∈ support ((oraclesWithAttempts sample attempt signer q).run state)) :
    badState metadata selected i threshold out.2 = true := by
  cases q with
  | inl n =>
      change out ∈ support ((fun answer => (answer, state)) <$>
        (unifSpec.query n : ProbComp (Fin (n + 1)))) at hout
      obtain ⟨answer, _, heq⟩ := OracleComp.mem_support_map_peel _ _ hout
      subst out
      exact hbad
  | inr q =>
      rcases q with ⟨ep, msg⟩
      change out ∈ support (signingOracleWithAttempts sample attempt signer (ep, msg) state)
        at hout
      cases hused : state.1 ep with
      | some record =>
          have heq : out = (none, state) :=
            OracleComp.eq_of_mem_support_pure (spec := unifSpec) _
              (by simpa [signingOracleWithAttempts, hused]
              using hout)
          subst out
          exact hbad
      | none =>
          simp only [signingOracleWithAttempts, hused, mem_support_bind_iff] at hout
          obtain ⟨coins, _, hpure⟩ := hout
          have heq := OracleComp.eq_of_mem_support_pure (spec := unifSpec) _ hpure
          subst out
          change privateBad metadata selected i threshold ||
            (state.2 ++ [BottomAttempt.mk ep msg (attempt ep msg coins)]).any
              (disclosedBad metadata selected i threshold) = true
          rw [List.any_append]
          simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.decide_eq_true,
            ← Bool.or_assoc]
          change badState metadata selected i threshold state || _ = true
          simp [hbad]

/-- Agreeing on all surviving current disclosures gives the same entire filtered oracle. -/
theorem filteredOracles_eq_of_disclosed_agreement {Coins : Type} (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (left right : Epoch S → M → Coins → Option (Signature R H S))
    (metadata : Metadata R H S) (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ)
    (hagree : ∀ ep msg coins, disclosedBad metadata selected i threshold
      ⟨ep, msg, attempt ep msg coins⟩ = false → left ep msg coins = right ep msg coins) :
    filteredOracles (oraclesWithAttempts sample attempt left)
      (badState metadata selected i threshold) =
    filteredOracles (oraclesWithAttempts sample attempt right)
      (badState metadata selected i threshold) := by
  funext q state
  cases state with
  | none => rfl
  | some state =>
      cases q with
      | inl n => rfl
      | inr q =>
          rcases q with ⟨ep, msg⟩
          change (fun out =>
              (if badState metadata selected i threshold out.2 then none else out.1,
                if badState metadata selected i threshold out.2 then none else some out.2)) <$>
              signingOracleWithAttempts sample attempt left (ep, msg) state =
            (fun out =>
              (if badState metadata selected i threshold out.2 then none else out.1,
                if badState metadata selected i threshold out.2 then none else some out.2)) <$>
              signingOracleWithAttempts sample attempt right (ep, msg) state
          cases hused : state.1 ep with
          | some record => simp only [signingOracleWithAttempts, hused]
          | none =>
              simp only [signingOracleWithAttempts, hused, map_bind, map_pure]
              apply bind_congr
              intro coins
              dsimp only [badState]
              by_cases hkill : (privateBad metadata selected i threshold ||
                  (state.2 ++ [BottomAttempt.mk ep msg (attempt ep msg coins)]).any
                    (disclosedBad metadata selected i threshold)) = true
              · simp only [hkill, ↓reduceIte]
              · have hflag : (privateBad metadata selected i threshold ||
                    (state.2 ++ [BottomAttempt.mk ep msg (attempt ep msg coins)]).any
                      (disclosedBad metadata selected i threshold)) = false :=
                  Bool.eq_false_of_not_eq_true hkill
                have hcurrent := disclosedBad_eq_false_of_append metadata selected i threshold
                  state.1 state.2 ⟨ep, msg, attempt ep msg coins⟩ hflag
                rw [hagree ep msg coins hcurrent]

/-- The absorbing filter preserves each good returned adaptive raw output and its full ledger. -/
theorem filtered_good_raw_output {Coins A : Type}
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S))
    (metadata : Metadata R H S) (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ)
    (program : OracleComp (FullSpec M H R S) A) (initial final : NativeState M H R S) (a : A)
    (hgood : badState metadata selected i threshold final = false) :
    let : MeasurableSpace (NativeState M H R S) := ⊤
    𝒟[(simulateQ (oraclesWithAttempts sample attempt signer) program).run initial] {(a, final)} =
    𝒟[(simulateQ (filteredOracles (oraclesWithAttempts sample attempt signer)
      (badState metadata selected i threshold)) program).run
      (if badState metadata selected i threshold initial then none else some initial)]
      {(a, some final)} := by
  let : MeasurableSpace (NativeState M H R S) := ⊤
  apply GXMSS.Reductions.FilteredSimulation.goodOutput_simulateQ_eq_filtered
    (oraclesWithAttempts sample attempt signer)
    (filteredOracles (oraclesWithAttempts sample attempt signer)
      (badState metadata selected i threshold))
    (badState metadata selected i threshold)
    (fun q out => if badState metadata selected i threshold out.2 then dummy q else out.1)
    ?_ ?_ ?_ ?_ program initial a final hgood
  · intro q answer state hstate
    simp [hstate]
  · exact badState_mono sample attempt signer metadata selected i threshold
  · intro q out hout
    change out ∈ support (pure (dummy q, none) : ProbComp _) at hout
    have heq := OracleComp.eq_of_mem_support_pure _ hout
    subst out
    rfl
  · intro q state _
    rfl

/-- The actual forest splice uses the native single-draw, first-request attempt logger. -/
@[expose] def spliceOracles (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) :
    QueryImpl (FullSpec M H R S) (StateT (NativeState M H R S) ProbComp) :=
  oraclesWithAttempts sampling.sampleBottom
    (bottomResult family sampling.bottom pp)
    (spliceSign hash family sampling pp selected i cut answer starts upperCoins)

/-- The honest splice is the source's actual enriched oracle, including failed bottom attempts. -/
theorem spliceOracles_honest (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (cut : ℕ)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) :
    spliceOracles hash family sampling pp selected i cut
      ((chainFamily hash pp).chain selected i 0 (cut + 1) (starts selected i))
      starts upperCoins =
    nativeOracles hash family sampling
      ⟨pp, starts, endpoints hash pp starts, upperCoins⟩ := by
  have hsign : spliceSign hash family sampling pp selected i cut
      ((chainFamily hash pp).chain selected i 0 (cut + 1) (starts selected i)) starts upperCoins =
      signWithCoins hash family sampling
        ⟨pp, starts, endpoints hash pp starts, upperCoins⟩ := by
    funext ep msg coins
    exact spliceSign_honest hash family sampling pp selected i cut starts upperCoins ep msg coins
  unfold spliceOracles oraclesWithAttempts nativeOracles nativeSigningOracle
  rw [hsign]
  rfl

/-- The full native splice oracle with absorbing selected-read rejection. -/
@[expose] def filteredSpliceOracles (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (threshold cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) :
    QueryImpl (FullSpec M H R S) (StateT (Option (NativeState M H R S)) ProbComp) :=
  filteredOracles (spliceOracles hash family sampling pp selected i cut answer starts upperCoins)
    (badState (prepare hash family sampling.internal pp
      (spliceEndpoints hash pp selected i cut answer starts) upperCoins) selected i threshold)

/-- Every surviving adaptive query agrees at adjacent cuts and retains full retry metadata. -/
theorem filteredSpliceOracles_advance (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (threshold cut : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (hn : cut + 2 ≤ 2 ^ S.w - 1) (hthreshold : cut + 2 ≤ threshold) :
    filteredSpliceOracles hash family sampling pp selected i threshold cut answer
      starts upperCoins =
      filteredSpliceOracles hash family sampling pp selected i threshold (cut + 1)
        ((chainFamily hash pp).chain selected i (cut + 1) 1 answer) starts upperCoins := by
  unfold filteredSpliceOracles spliceOracles
  rw [← prepare_advance hash family sampling.internal pp selected i cut answer starts upperCoins hn]
  apply filteredOracles_eq_of_disclosed_agreement
  intro ep msg coins hbad
  apply spliceSign_advance hash family sampling pp selected i cut answer starts upperCoins ep msg
    coins hn
  intro p j position hread hp hj
  exact hthreshold.trans (reads_safe_of_disclosedBad_eq_false family sampling pp ep msg coins
    _ selected i threshold hbad p j position hread hp hj)

/-- At zero cut the entire filtered oracle ignores its old start, including failed calls. -/
theorem filteredSpliceOracles_zero_start_update (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ) (answer : H)
    (starts : OTSPosition S → Fin S.v → H) (replacement : H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (hn : 0 < 2 ^ S.w - 1) (hthreshold : 0 < threshold) :
    filteredSpliceOracles hash family sampling pp selected i threshold 0 answer
      (Function.update starts selected (Function.update (starts selected) i replacement))
      upperCoins =
    filteredSpliceOracles hash family sampling pp selected i threshold 0 answer
      starts upperCoins := by
  unfold filteredSpliceOracles spliceOracles
  rw [prepare_zero_start_update hash family sampling.internal pp selected i answer starts
    replacement upperCoins hn]
  apply filteredOracles_eq_of_disclosed_agreement
  intro ep msg coins hbad
  apply spliceSign_zero_start_update hash family sampling pp selected i answer starts replacement
    upperCoins ep msg coins hn
  intro p j position hread hp hj
  exact hthreshold.trans_le (reads_safe_of_disclosedBad_eq_false family sampling pp ep msg coins
    _ selected i threshold hbad p j position hread hp hj)

/-- Full filtered adaptive interaction, exposing the complete first-request and retry ledgers.
The raw result omits hidden chain starts, which are irrelevant to the surviving response law. -/
@[expose] def runFilteredRaw (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (adv : SchemeAdversary PP H M R S) (pp : PP) (selected : OTSPosition S) (i : Fin S.v)
    (threshold cut : ℕ) (answer : H) (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) :
    ProbComp (SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S) ×
      Option (NativeState M H R S)) :=
  let metadata := prepare hash family sampling.internal pp
    (spliceEndpoints hash pp selected i cut answer starts) upperCoins
  let pk : GXMSS.PublicKey PP H := ⟨metadata.roots (topTree S), pp⟩
  let initial : NativeState M H R S := (SyncSignatureUnforgeability.emptyHistory, [])
  (simulateQ (filteredSpliceOracles hash family sampling pp selected i threshold cut answer
    starts upperCoins) (adv.forge pk)).run
      (if badState metadata selected i threshold initial then none else some initial)

/-- Adjacent-cut equality holds for the entire adaptive raw interaction, including rejection. -/
theorem runFilteredRaw_advance (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (adv : SchemeAdversary PP H M R S) (pp : PP) (selected : OTSPosition S) (i : Fin S.v)
    (threshold cut : ℕ) (answer : H) (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (hn : cut + 2 ≤ 2 ^ S.w - 1) (hthreshold : cut + 2 ≤ threshold) :
    runFilteredRaw hash family sampling adv pp selected i threshold cut answer starts upperCoins =
      runFilteredRaw hash family sampling adv pp selected i threshold (cut + 1)
        ((chainFamily hash pp).chain selected i (cut + 1) 1 answer) starts upperCoins := by
  unfold runFilteredRaw
  rw [prepare_advance hash family sampling.internal pp selected i cut answer starts upperCoins hn,
    filteredSpliceOracles_advance hash family sampling pp selected i threshold cut answer starts
      upperCoins hn hthreshold]

/-- Zero-cut independence holds for the whole adaptive raw interaction and both private ledgers. -/
theorem runFilteredRaw_zero_start_update (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (adv : SchemeAdversary PP H M R S) (pp : PP) (selected : OTSPosition S) (i : Fin S.v)
    (threshold : ℕ) (answer : H) (starts : OTSPosition S → Fin S.v → H) (replacement : H)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (hn : 0 < 2 ^ S.w - 1) (hthreshold : 0 < threshold) :
    runFilteredRaw hash family sampling adv pp selected i threshold 0 answer
      (Function.update starts selected (Function.update (starts selected) i replacement))
      upperCoins =
    runFilteredRaw hash family sampling adv pp selected i threshold 0 answer starts upperCoins := by
  unfold runFilteredRaw
  rw [prepare_zero_start_update hash family sampling.internal pp selected i answer starts
      replacement upperCoins hn,
    filteredSpliceOracles_zero_start_update hash family sampling pp selected i threshold answer
      starts replacement upperCoins hn hthreshold]

/-- Source observations can inspect all current public structure, canonical private references,
the forgery, and both native ledgers, without inspecting hidden starts directly. -/
abbrev Observation (M H R : Type) (S : Shape) :=
  H → (OTSPosition S → Fin S.v → H) → Metadata R H S →
    (UpperPosition S → Option (GXMSS.Signature R H S.h S.v)) →
    SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S) →
    NativeState M H R S → Bool

/-- Observe the current forest continuation; killed states have no selected winning observation.
The private-upper guard makes every inspected canonical reference prefix safe. -/
@[expose] def runObserved (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (adv : SchemeAdversary PP H M R S) (pp : PP) (selected : OTSPosition S) (i : Fin S.v)
    (threshold cut : ℕ) (answer : H) (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) (observe : Observation M H R S) :
    ProbComp Bool :=
  let ends := spliceEndpoints hash pp selected i cut answer starts
  let metadata := prepare hash family sampling.internal pp ends upperCoins
  let references := canonicalReferences metadata
    (splicePrefixes hash pp selected i cut answer starts)
  let selectedResponse := splicePrefixes hash pp selected i cut answer starts selected i threshold
  do
    let out ← runFilteredRaw hash family sampling adv pp selected i threshold cut answer
      starts upperCoins
    pure (if privateBad metadata selected i threshold then false else
      out.2.elim false fun state =>
        observe selectedResponse ends metadata references out.1 state)

/-- Guarded unfiltered returned events are preserved by the actual absorbing adaptive filter. -/
theorem guarded_unfiltered_mass_le_observed (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (adv : SchemeAdversary PP H M R S) (pp : PP) (selected : OTSPosition S) (i : Fin S.v)
    (threshold cut : ℕ) (answer : H) (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) (observe : Observation M H R S) :
    let ends := spliceEndpoints hash pp selected i cut answer starts
    let metadata := prepare hash family sampling.internal pp ends upperCoins
    let references := canonicalReferences metadata
      (splicePrefixes hash pp selected i cut answer starts)
    let response := splicePrefixes hash pp selected i cut answer starts selected i threshold
    let pk : GXMSS.PublicKey PP H := ⟨metadata.roots (topTree S), pp⟩
    let initial : NativeState M H R S := (SyncSignatureUnforgeability.emptyHistory, [])
    𝒟[(fun out => if badState metadata selected i threshold out.2 then false else
      observe response ends metadata references out.1 out.2) <$>
      (simulateQ (spliceOracles hash family sampling pp selected i cut answer starts upperCoins)
        (adv.forge pk)).run initial] {true} ≤
      𝒟[runObserved hash family sampling adv pp selected i threshold cut answer starts upperCoins
        observe] {true} := by
  classical
  dsimp only
  let ends := spliceEndpoints hash pp selected i cut answer starts
  let metadata := prepare hash family sampling.internal pp ends upperCoins
  let references := canonicalReferences metadata
    (splicePrefixes hash pp selected i cut answer starts)
  let response := splicePrefixes hash pp selected i cut answer starts selected i threshold
  let pk : GXMSS.PublicKey PP H := ⟨metadata.roots (topTree S), pp⟩
  let initial : NativeState M H R S := (SyncSignatureUnforgeability.emptyHistory, [])
  let event := fun out :
      SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S) × NativeState M H R S =>
    if badState metadata selected i threshold out.2 then false else
      observe response ends metadata references out.1 out.2
  let raw := (simulateQ
    (spliceOracles hash family sampling pp selected i cut answer starts upperCoins)
    (adv.forge pk)).run initial
  let : MeasurableSpace
      (SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S)) := ⊤
  let : MeasurableSpace (NativeState M H R S) := ⊤
  let : MeasurableSpace
      (SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S) ×
        NativeState M H R S) := ⊤
  let : MeasurableSpace
      (SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S) ×
        Option (NativeState M H R S)) := ⊤
  have heq := GXMSS.Reductions.FilteredSimulation.goodEvent_eq_filtered raw
    (runFilteredRaw hash family sampling adv pp selected i threshold cut answer starts upperCoins)
    (badState metadata selected i threshold) event (by
      intro out hout
      by_cases hbad : badState metadata selected i threshold out.2 = true
      · simp [event, hbad] at hout
      · exact Bool.eq_false_of_not_eq_true hbad) (by
      intro out hgood
      simpa only [← prEvent_eq_evalDist_singleton, raw, runFilteredRaw,
        filteredSpliceOracles, spliceOracles, pk, metadata, ends, initial, Prod.mk.eta] using
        filtered_good_raw_output sampling.sampleBottom
        (bottomResult family sampling.bottom pp)
        (spliceSign hash family sampling pp selected i cut answer starts upperCoins)
        metadata selected i threshold (adv.forge pk) initial out.2 out.1 hgood)
  change 𝒟[event <$> raw] {true} ≤ _
  rw [heq]
  unfold runObserved
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (measurableSet_singleton true)
  intro out _
  cases hs : out.2 with
  | none => simp
  | some state =>
      by_cases hgood : badState metadata selected i threshold state = false
      · have hp : privateBad metadata selected i threshold = false :=
          (Bool.or_eq_false_iff.mp hgood).1
        dsimp only [metadata, ends] at hp
        simp only [event, hgood, hp, Option.elim_some,
          ends, metadata, references, response]
        exact le_rfl
      · have hb := Bool.eq_true_of_not_eq_false hgood
        simp [event, hb]

/-- Whole observed adaptive programs agree across adjacent cuts, including private references. -/
theorem runObserved_advance (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (adv : SchemeAdversary PP H M R S) (pp : PP) (selected : OTSPosition S) (i : Fin S.v)
    (threshold cut : ℕ) (answer : H) (starts : OTSPosition S → Fin S.v → H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) (observe : Observation M H R S)
    (hn : cut + 2 ≤ 2 ^ S.w - 1) (hthreshold : cut + 2 ≤ threshold) :
    runObserved hash family sampling adv pp selected i threshold cut answer
      starts upperCoins observe =
      runObserved hash family sampling adv pp selected i threshold (cut + 1)
        ((chainFamily hash pp).chain selected i (cut + 1) 1 answer) starts upperCoins observe := by
  have hends := GXMSS.Reductions.ChainContinuation.spliceEndpoints_advance
    (chainFamily hash pp) (2 ^ S.w - 1) selected i cut answer starts hn
  change spliceEndpoints hash pp selected i cut answer starts =
    spliceEndpoints hash pp selected i (cut + 1)
      ((chainFamily hash pp).chain selected i (cut + 1) 1 answer) starts at hends
  have hresponse := GXMSS.Reductions.ChainContinuation.spliceValue_advance
    (chainFamily hash pp) selected i cut answer starts selected i threshold
    (fun _ _ => hthreshold)
  change splicePrefixes hash pp selected i cut answer starts selected i threshold =
    splicePrefixes hash pp selected i (cut + 1)
      ((chainFamily hash pp).chain selected i (cut + 1) 1 answer) starts selected i threshold
    at hresponse
  unfold runObserved
  dsimp only
  by_cases hbad : privateBad (prepare hash family sampling.internal pp
      (spliceEndpoints hash pp selected i cut answer starts) upperCoins)
      selected i threshold = false
  · rw [canonicalReferences_advance hash family sampling.internal pp selected i threshold cut
      answer starts upperCoins hn hthreshold hbad,
      runFilteredRaw_advance hash family sampling adv pp selected i threshold cut answer starts
        upperCoins hn hthreshold, hends, hresponse]
  · have htrue := Bool.eq_true_of_not_eq_false hbad
    rw [runFilteredRaw_advance hash family sampling adv pp selected i threshold cut answer starts
      upperCoins hn hthreshold, hends] at *
    simp only [htrue, ↓reduceIte]

/-- Whole observed adaptive programs at zero cut ignore the old selected start. -/
theorem runObserved_zero_start_update (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (adv : SchemeAdversary PP H M R S) (pp : PP) (selected : OTSPosition S) (i : Fin S.v)
    (threshold : ℕ) (answer : H) (starts : OTSPosition S → Fin S.v → H) (replacement : H)
    (upperCoins : UpperPosition S → sampling.internal.Coins) (observe : Observation M H R S)
    (hn : 0 < 2 ^ S.w - 1) (hthreshold : 0 < threshold) :
    runObserved hash family sampling adv pp selected i threshold 0 answer
      (Function.update starts selected (Function.update (starts selected) i replacement))
      upperCoins observe =
    runObserved hash family sampling adv pp selected i threshold 0 answer
      starts upperCoins observe := by
  have hends := GXMSS.Reductions.ChainContinuation.spliceEndpoints_zero_start_update
    (chainFamily hash pp) (2 ^ S.w - 1) selected i answer starts replacement hn
  change spliceEndpoints hash pp selected i 0 answer
      (Function.update starts selected (Function.update (starts selected) i replacement)) =
    spliceEndpoints hash pp selected i 0 answer starts at hends
  have hresponse := GXMSS.Reductions.ChainContinuation.spliceValue_zero_start_update
    (chainFamily hash pp) selected i answer starts replacement selected i threshold
    (fun _ _ => hthreshold)
  change splicePrefixes hash pp selected i 0 answer
      (Function.update starts selected (Function.update (starts selected) i replacement))
      selected i threshold =
    splicePrefixes hash pp selected i 0 answer starts selected i threshold at hresponse
  unfold runObserved
  dsimp only
  by_cases hbad : privateBad (prepare hash family sampling.internal pp
      (spliceEndpoints hash pp selected i 0 answer starts) upperCoins) selected i threshold = false
  · rw [canonicalReferences_zero_start_update hash family sampling.internal pp selected i threshold
      answer starts replacement upperCoins hn hthreshold hbad,
      runFilteredRaw_zero_start_update hash family sampling adv pp selected i threshold answer
        starts replacement upperCoins hn hthreshold, hends, hresponse]
  · have htrue := Bool.eq_true_of_not_eq_false hbad
    rw [runFilteredRaw_zero_start_update hash family sampling adv pp selected i threshold answer
      starts replacement upperCoins hn hthreshold, hends]
    simp only [htrue, ↓reduceIte]

/-- The actual full-forest start sampler has the uniform nested finite-table law. -/
theorem sampleStarts_uniform_measure [SampleableType H]
    [MeasurableSpace H] [MeasurableSingletonClass H] :
    𝒟[sampleStarts (H := H) S] = ProbabilityTheory.uniformOn Set.univ := by
  classical
  let : Fintype (OTSPosition S) := Fintype.ofFinite _
  unfold sampleStarts
  exact evalDist_mPi_const_uniform (Fin.mOfFn S.v fun _ => ($ᵗ H : ProbComp H))
    (evalDist_mOfFn_const_uniform S.v ($ᵗ H) SampleableType.evalDist_uniformSample)

/-- Whole adaptive zero-cut continuations allow independent sampling of the first chain image. -/
theorem filtered_zero_real_source_mass [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ)
    (upperCoins : UpperPosition S → sampling.internal.Coins)
    (observe : (SyncSignatureUnforgeability.Forgery (Epoch S) M (Signature R H S) ×
      Option (NativeState M H R S)) → Bool)
    (hn : 0 < 2 ^ S.w - 1) (hthreshold : 0 < threshold) :
    𝒟[do
      let starts ← sampleStarts S
      let answer := (chainFamily hash pp).chain selected i 0 1 (starts selected i)
      let out ← runFilteredRaw hash family sampling adv pp selected i threshold 0 answer
        starts upperCoins
      pure (observe out)] {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← sampleStarts S
      let out ← runFilteredRaw hash family sampling adv pp selected i threshold 0
        ((chainFamily hash pp).chain selected i 0 1 x) starts upperCoins
      pure (observe out)] {true} := by
  let : MeasurableSpace H := ⊤
  have h := GXMSS.Reductions.ReturnedMass.independent_coordinate_image_mass
    (sampleStarts S) sampleStarts_uniform_measure selected i
    ((chainFamily hash pp).chain selected i 0 1)
    (fun answer starts => observe <$>
      runFilteredRaw hash family sampling adv pp selected i threshold 0 answer starts upperCoins)
    (fun answer starts x => congrArg (fun program => 𝒟[observe <$> program] {true})
      (runFilteredRaw_zero_start_update hash family sampling adv pp selected i threshold answer
        starts x upperCoins hn hthreshold))
  simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc] using h

/-- Current endpoints, canonical references and both ledgers participate in the zero-cut coupling.
No observer is allowed to inspect the hidden old start directly. -/
theorem observed_zero_real_source_mass [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (threshold : ℕ)
    (upperCoins : UpperPosition S → sampling.internal.Coins) (observe : Observation M H R S)
    (hn : 0 < 2 ^ S.w - 1) (hthreshold : 0 < threshold) :
    𝒟[do
      let starts ← sampleStarts S
      runObserved hash family sampling adv pp selected i threshold 0
        ((chainFamily hash pp).chain selected i 0 1 (starts selected i))
        starts upperCoins observe] {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← sampleStarts S
      runObserved hash family sampling adv pp selected i threshold 0
        ((chainFamily hash pp).chain selected i 0 1 x) starts upperCoins observe] {true} := by
  let : MeasurableSpace H := ⊤
  exact GXMSS.Reductions.ReturnedMass.independent_coordinate_image_mass
    (sampleStarts S) sampleStarts_uniform_measure selected i
    ((chainFamily hash pp).chain selected i 0 1)
    (fun answer starts =>
      runObserved hash family sampling adv pp selected i threshold 0 answer starts upperCoins
        observe)
    (fun answer starts x => congrArg (fun program => 𝒟[program] {true})
      (runObserved_zero_start_update hash family sampling adv pp selected i threshold answer
        starts x upperCoins observe hn hthreshold))

/-- A fixed-cut real or ideal adaptive experiment over the actual forest and persistent tapes. -/
@[expose] noncomputable def filteredCutProgram [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (g cut : ℕ) (world : SM_DT_UD_World)
    (observe : Observation M H R S) : ProbComp Bool := do
  let starts ← sampleStarts S
  let upperCoins ← sampleUpperCoins S sampling.sampleInternal
  let x ← ($ᵗ H : ProbComp H)
  let answer := match world with
    | .real => (chainFamily hash pp).chain selected i cut 1 x
    | .ideal => x
  runObserved hash family sampling adv pp selected i (g + 1) cut answer
    starts upperCoins observe

/-- The actual ideal continuation at one cut is the next actual real continuation. -/
theorem filteredCutProgram_ideal_eq_real_succ [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (g cut : ℕ)
    (observe : Observation M H R S)
    (hg : g < 2 ^ S.w - 1) (hcut : cut < g) :
    filteredCutProgram hash family sampling adv pp selected i g cut .ideal observe =
      filteredCutProgram hash family sampling adv pp selected i g (cut + 1) .real observe := by
  unfold filteredCutProgram
  apply bind_congr
  intro starts
  apply bind_congr
  intro upperCoins
  apply bind_congr
  intro x
  dsimp only
  rw [runObserved_advance hash family sampling adv pp selected i (g + 1) cut x starts
    upperCoins observe (by omega) (by omega)]

/-- Exact averaged returned-mass telescope for the actual forest cut programs.
Unused indices return false while retaining the complete `D-1` sampling domain. -/
theorem filteredCutProgram_telescope [SampleableType H] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : SchemeAdversary PP H M R S) (pp : PP)
    (selected : OTSPosition S) (i : Fin S.v) (g : ℕ)
    (observe : Observation M H R S) (hg : g < 2 ^ S.w - 1) :
    let program := filteredCutProgram hash family sampling adv pp selected i g
    𝒟[program 0 .real observe] {true} + ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) * 𝒟[do
      let j ← ($ᵗ (Fin (2 ^ S.w - 1)) : ProbComp (Fin (2 ^ S.w - 1)))
      if j.val < g then program j.val .ideal observe else pure false] {true} =
    𝒟[program g .real observe] {true} + ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) * 𝒟[do
      let j ← ($ᵗ (Fin (2 ^ S.w - 1)) : ProbComp (Fin (2 ^ S.w - 1)))
      if j.val < g then program j.val .real observe else pure false] {true} := by
  apply GXMSS.Reductions.HybridTelescope.uniform_prefix_true_mass_telescope
    (fun j => filteredCutProgram hash family sampling adv pp selected i g j .real observe)
    (fun j => filteredCutProgram hash family sampling adv pp selected i g j .ideal observe)
    (2 ^ S.w - 1) g (Nat.le_of_lt hg)
  intro j hj
  rw [filteredCutProgram_ideal_eq_real_succ hash family sampling adv pp selected i g j observe
    hg hj]

end GXMSS.Hypertree.Security.ChainMass
