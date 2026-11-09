/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.ReturnedMass
public import HashSig.GXMSS.Security.Auxiliary.HybridTelescope
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
public import HashSig.GXMSS.Security.Reductions.EncodingCollision
import all HashSig.GXMSS.Security.Reductions.EncodingCollision
public import HashSig.GXMSS.Security.Reductions.Problems
import all HashSig.GXMSS.Security.Reductions.Problems
public import HashSig.GXMSS.Security.Reductions.TargetCollision
import all HashSig.GXMSS.Security.Reductions.TargetCollision
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Selected chain source probabilities

Uniform selector probabilities and source winning masses are related by exact finite-cardinality
laws. Start resampling and filtered zero-cut identities support the native chain hybrid.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

/-- One uniform selector succeeds with exactly inverse-cardinality probability on each returned
Game 4 win under the explicit no-maximum-output premise. -/
theorem jointChainGuess_probability [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (hnonmax : NoMaximumOutput enc)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv)) :
    Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
      jointChainObservation hash enc K (guess, out) = true] =
      if gameFourObservation hash enc K out = true then
        (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ else 0 := by
  apply ReturnedMass.uniform_selector_probability
  · intro hwin
    exact jointChainObservation_singleton hash enc K adv hnonmax out hout hwin
  · intro guess hguess
    exact jointChainObservation_implies_gameFour hash enc K guess out hguess
/-- Conditional on one returned source result, the actual uniform Game 5 guess passes with
exactly inverse-cardinality mass when that result is a successful Game 4 win. -/
theorem gameFiveGuess_probability [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv)) :
    Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
      gameFiveObservation hash enc K (guess, out) = true] =
      if successfulGameFourObservation hash enc K out = true then
        (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ else 0 := by
  apply ReturnedMass.uniform_selector_probability
  · intro hwin
    obtain ⟨msg, sig, honestWord, forgedWord, i, hsource, hhonest, hforged, hi⟩ :=
      successfulGameFour_designated_coordinate hash enc K adv out hout hwin
    exact gameFiveObservation_successful_singleton
      hash enc K out msg sig honestWord forgedWord i hsource hhonest hforged hi
      (by simpa [successfulGameFourObservation, hsource] using hwin)
  · intro guess hguess
    exact gameFiveObservation_implies_successfulGameFour hash enc K guess out hguess
/-- The actual Game 5 native returned winning mass is exactly the successful-record Game 4
mass divided by the finite guess count. The source program's unreturned mass is unchanged. -/
theorem gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    gameFiveAdvantage hash enc K hv hw adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ *
        successfulGameFourMass hash enc K adv := by
  have : NeZero v := ⟨Nat.ne_of_gt hv⟩
  have : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : MeasurableSpace (Result PP H M R h v) := ⊤
  let source := sourceProgram hash enc K adv
  let c : ℝ≥0∞ := (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹
  have hmass : successfulGameFourMass hash enc K adv =
      𝒟[source] {out | successfulGameFourObservation hash enc K out = true} := by
    simp only [successfulGameFourMass, ProbCompRuntime.probComp_evalDist]
    rw [evalDist_map_apply source Measurable.of_discrete (measurableSet_singleton true)]
    rfl
  have hswap :
      𝒟[gameFiveObservation hash enc K <$> gameFive hash enc K hv hw adv] =
        𝒟[do
          let out ← source
          let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
          return gameFiveObservation hash enc K (guess, out)] := by
    simp only [gameFive, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_bind_swap _ _ _
  have hconditional : ∀ out ∈ support source,
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return gameFiveObservation hash enc K (guess, out)] {true} =
        if successfulGameFourObservation hash enc K out = true then c else 0 := by
    intro out hout
    have hprob := gameFiveGuess_probability hash enc K adv out hout
    have hobs : Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
        gameFiveObservation hash enc K (guess, out) = true] =
        𝒟[(fun guess => gameFiveObservation hash enc K (guess, out)) <$>
          ($ᵗ (Guess h w v) : ProbComp (Guess h w v))] {true} := by
      exact (prEvent_map _ (fun guess => gameFiveObservation hash enc K (guess, out))
        (fun b => b = true)).symm.trans (prEvent_eq_evalDist_singleton _ true)
    rw [hobs] at hprob
    simpa only [c, map_eq_bind_pure_comp, Function.comp_def] using hprob
  unfold gameFiveAdvantage gameFiveOutputMeasure
  rw [ProbCompRuntime.probComp_evalDist, hswap,
    ReturnedMass.bind_true_mass_eq_mul_event source _ _ c hconditional, ← hmass]
/-- On successful returned Game 4 records, the exact finite guess factor recovers the native
Game 4 mass from the actual Game 5 returned winning mass. -/
theorem successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    successfulGameFourMass hash enc K adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞) *
        gameFiveAdvantage hash enc K hv hw adv := by
  have hcard : 0 < Fintype.card (Guess h w v) := by
    rw [guess_cardinality]
    have hpow : 0 < 2 ^ h := pow_pos (by omega) _
    have hposition : 0 < 2 ^ w - 1 := by
      have := Nat.one_lt_two_pow (by omega : w ≠ 0)
      omega
    positivity
  have hne : (Fintype.card (Guess h w v) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcard
  have htop : (Fintype.card (Guess h w v) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  rw [gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
    hash enc K hv hw adv, ENNReal.mul_inv_cancel_left hne htop]
/-- Filtering preserves exactly the selected true mass of a fixed spliced adaptive run. -/
private theorem runContextSpliced_selectedMass_eq_filtered
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (observe : Result PP H M R h v → Bool)
    (hobserve : ∀ out, observe out = true →
      badSelectedHistory enc out.pk.seed selector out.history = false) :
    𝒟[(fun out => observe out) <$>
      runContextSpliced hash enc K ctx adv pp splice answer starts] {true} =
    𝒟[(fun out => out.elim false
      (fun result => observe result)) <$>
      runContextFilteredSpliced hash enc K ctx adv pp selector splice answer starts] {true} := by
  classical
  let endpoints := splicedEndpoints hash pp splice answer starts
  let pk : GXMSS.PublicKey PP H := ⟨ctx.root pp endpoints, pp⟩
  let sk : GXMSS.SecretKey PP H h v := ⟨pp, starts, endpoints⟩
  let original : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      contextSplicedSigningOracle hash enc K ctx pp splice answer starts endpoints
  let filtered : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) +
      contextFilteredSplicedSigningOracle hash enc K ctx pp selector splice answer starts endpoints
  let raw := (simulateQ original (adv.forge pk)).run
    SyncSignatureUnforgeability.emptyHistory
  let rawFiltered := (simulateQ filtered (adv.forge pk)).run
    (some SyncSignatureUnforgeability.emptyHistory)
  let event : SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v) ×
      SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) → Bool :=
    fun z => observe ⟨pk, sk, z.1, z.2⟩
  let bad := badSelectedHistory (H := H) enc pp selector
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.History (Epoch h) M
    (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v) ×
    SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v) ×
    Option (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))) := ⊤
  have hgood : ∀ z, event z = true → bad z.2 = false := by
    intro z hz
    have h := hobserve
      (⟨pk, sk, z.1, z.2⟩ : Result PP H M R h v) hz
    simpa [bad, pk] using h
  have hpoint : ∀ z, bad z.2 = false →
      𝒟[raw] {z} = 𝒟[rawFiltered] {(z.1, some z.2)} := by
    intro z hz
    simpa only [← prEvent_eq_evalDist_singleton, raw, rawFiltered, original, filtered,
      endpoints, pk, bad] using
      contextSplicedFiltered_good_raw_output hash enc K ctx adv pp selector splice answer
        starts z.1 z.2 hz
  have heq := goodEvent_eq_filtered raw rawFiltered bad event hgood hpoint
  convert heq using 1
  · simp only [runContextSpliced, raw, event, original, endpoints, pk, sk,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · simp only [runContextFilteredSpliced, rawFiltered, event, filtered, endpoints,
      pk, sk, map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro x
    cases x.2 <;> rfl
private theorem runSpliced_selectedMass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) :
    𝒟[(fun out => jointChainObservation hash enc K (selector, out)) <$>
      runSpliced hash enc K adv pp splice answer starts] {true} =
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector splice answer starts] {true} := by
  exact runContextSpliced_selectedMass_eq_filtered hash enc K (completeChainContext hash)
    adv pp selector splice answer starts
    (fun out => jointChainObservation hash enc K (selector, out))
    (jointChainObservation_not_badSelectedHistory hash enc K selector)
/-- The nested finite start sampler has the uniform product measure on complete arrays. -/
private theorem sampleStarts_uniform_measure [SampleableType H]
    [MeasurableSpace H] [MeasurableSingletonClass H] :
    𝒟[GXMSS.sampleStarts H h v] = ProbabilityTheory.uniformOn Set.univ := by
  classical
  unfold GXMSS.sampleStarts
  exact evalDist_mOfFn_const_uniform (2 ^ h)
    (Fin.mOfFn v (fun _ => ($ᵗ H : ProbComp H)))
    (evalDist_mOfFn_const_uniform v ($ᵗ H)
      SampleableType.evalDist_uniformSample)
/-- Pointwise equality of returned event masses integrates over a common discrete draw. -/
private theorem evalDist_bind_event_eq_of_discrete
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β)
    (event : Set β) (hevent : MeasurableSet event)
    (hfg : ∀ a, 𝒟[f a] event = 𝒟[g a] event) :
    𝒟[mx >>= f] event = 𝒟[mx >>= g] event := by
  exact ReturnedMass.evalDist_bind_event_eq_of_discrete mx f g event hevent hfg
/-- A position-zero splice never reads its old selected start at any positive chain position. -/
private theorem splicedChainValue_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (ep : Epoch h) (i : Fin v) (position : ℕ)
    (hzero : (guessedPosition guess).val = 0) (hpos : 0 < position) :
    splicedChainValue hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      ep i position =
    splicedChainValue hash pp guess answer starts ep i position := by
  simpa only [splicedChainValue, hzero, chainFamily] using
    ChainContinuation.spliceValue_zero_start_update (chainFamily hash pp)
      (guessedEpoch guess) (guessedChain guess) answer starts x ep i position
      (fun _ _ => hpos)
/-- Updating the old selected start leaves the endpoint array of a zero splice fixed. -/
private theorem splicedEndpoints_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1) :
    splicedEndpoints hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x)) =
      splicedEndpoints hash pp guess answer starts := by
  funext ep i
  exact splicedChainValue_zero_start_update hash pp guess answer starts x ep i
    (2 ^ w - 1) hzero hn
/-- Every surviving selected-epoch signature at a zero splice has a positive selected digit. -/
private theorem contextSplicedSignatureOfWord_zero_start_update
    (hash : HashInstance PP T X H h w v) (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hword : ep = guessedEpoch guess →
      0 < (wr.1 (guessedChain guess)).val) :
    contextSplicedSignatureOfWord hash ctx pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) ep wr =
    contextSplicedSignatureOfWord hash ctx pp guess answer starts
      (splicedEndpoints hash pp guess answer starts) ep wr := by
  have h := (contextWordContinuation ctx pp ep wr).materialize_zero_start_update
    (chainFamily hash pp) (2 ^ w - 1) (guessedEpoch guess) (guessedChain guess)
    answer starts x () hn (by
      intro c i position hread he hi
      have hep : ep = guessedEpoch guess := hread.1.symm.trans he
      have hbound := hword hep
      have hposition : position = (wr.1 (guessedChain guess)).val := by
        simpa only [hi] using hread.2
      omega)
  simpa only [contextWordContinuation, contextSplicedSignatureOfWord, splicedChainValue,
    splicedEndpoints, hzero, chainFamily] using h
/-- At a zero splice the filtered signing handler is independent of the old selected start. -/
private theorem contextFilteredSplicedSigningOracle_zero_start_update
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (pp : PP) (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    contextFilteredSplicedSigningOracle hash enc K ctx pp selector guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) =
    contextFilteredSplicedSigningOracle hash enc K ctx pp selector guess answer starts
      (splicedEndpoints hash pp guess answer starts) := by
  rw [splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn]
  funext q state
  cases state with
  | none => rfl
  | some history =>
    rcases q with ⟨ep, msg⟩
    by_cases hused : history ep = none
    · by_cases hactive : ctx.activity ep = true
      · simp only [contextFilteredSplicedSigningOracle, hused, hactive, ↓reduceIte]
        apply bind_congr
        intro wr
        cases wr with
        | none => rfl
        | some value =>
          by_cases hbad : ep = guessedEpoch selector ∧
              (value.1 (guessedChain selector)).val < (guessedPosition selector).val + 1
          · simp [hbad]
          · have hword : ep = guessedEpoch guess →
                0 < (value.1 (guessedChain guess)).val := by
              intro hep
              have hnot : ¬(value.1 (guessedChain selector)).val <
                  (guessedPosition selector).val + 1 := by
                intro hlt; exact hbad ⟨by simpa only [hepoch] using hep, hlt⟩
              rw [hchain] at hnot
              omega
            have hsig := contextSplicedSignatureOfWord_zero_start_update hash ctx pp guess answer
              starts x ep value hzero hn hword
            rw [splicedEndpoints_zero_start_update hash pp guess answer starts x
              hzero hn] at hsig
            simp only [hsig]
      · simp [contextFilteredSplicedSigningOracle, hused, hactive]
    · cases hrecord : history ep with
      | none => exact False.elim (hused hrecord)
      | some record => simp [contextFilteredSplicedSigningOracle, hrecord]
private theorem splicedSignatureOfWord_zero_start_update
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hword : ep = guessedEpoch guess →
      0 < (wr.1 (guessedChain guess)).val) :
    splicedSignatureOfWord hash pp guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) ep wr =
    splicedSignatureOfWord hash pp guess answer starts
      (splicedEndpoints hash pp guess answer starts) ep wr := by
  exact contextSplicedSignatureOfWord_zero_start_update hash (completeChainContext hash)
    pp guess answer starts x ep wr hzero hn hword
/-- At a zero splice the filtered signing handler is independent of the old selected start. -/
private theorem filteredSplicedSigningOracle_zero_start_update
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (pp : PP) (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    filteredSplicedSigningOracle hash enc K pp selector guess answer
      (Function.update starts (guessedEpoch guess)
        (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))
      (splicedEndpoints hash pp guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))) =
    filteredSplicedSigningOracle hash enc K pp selector guess answer starts
      (splicedEndpoints hash pp guess answer starts) := by
  exact contextFilteredSplicedSigningOracle_zero_start_update hash enc K
    (completeChainContext hash) pp selector guess answer starts x hzero hn hepoch hchain
/-- The zero-cut filtered winning mass is independent of the old selected start. -/
private theorem runContextFilteredSpliced_zero_start_update_mass
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (observe : GXMSS.PublicKey PP H → (Epoch h → Fin v → H) →
      SyncSignatureUnforgeability.Forgery (Epoch h) M (GXMSS.Signature R H h v) →
      SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v) → Bool)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    𝒟[(fun out => out.elim false
      (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)) <$>
      runContextFilteredSpliced hash enc K ctx adv pp selector guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))]
      {true} =
    𝒟[(fun out => out.elim false
      (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)) <$>
      runContextFilteredSpliced hash enc K ctx adv pp selector guess answer starts] {true} := by
  have hend := splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn
  have hhandler := contextFilteredSplicedSigningOracle_zero_start_update
    hash enc K ctx pp selector guess answer starts x hzero hn hepoch hchain
  rw [hend] at hhandler
  apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
  unfold runContextFilteredSpliced
  dsimp only
  rw [hend, hhandler]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  apply bind_congr
  intro z
  cases z with
  | mk forgery state =>
    cases state <;> rfl
private theorem runFilteredSpliced_zero_start_update_mass
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector guess : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (x : H)
    (hzero : (guessedPosition guess).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch guess)
    (hchain : guessedChain selector = guessedChain guess) :
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector guess answer
        (Function.update starts (guessedEpoch guess)
          (Function.update (starts (guessedEpoch guess)) (guessedChain guess) x))]
      {true} =
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector guess answer starts] {true} := by
  have hend := splicedEndpoints_zero_start_update hash pp guess answer starts x hzero hn
  have hhandler := filteredSplicedSigningOracle_zero_start_update
    hash enc K pp selector guess answer starts x hzero hn hepoch hchain
  rw [hend] at hhandler
  apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
  unfold runFilteredSpliced
  dsimp only
  rw [hend, hhandler]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
  apply bind_congr
  intro z
  cases z with
  | mk forgery state =>
    cases state <;> rfl

/-- At a fixed seed and selector, a real first-step challenge can be sampled independently of
the otherwise unused old selected start, without changing returned selected winning mass. -/
private theorem context_filteredZero_real_source_mass
    [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v)
    (observe : GXMSS.PublicKey PP H → (Epoch h → Fin v → H) →
      SyncSignatureUnforgeability.Forgery (Epoch h) M (GXMSS.Signature R H h v) →
      SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v) → Bool)
    (hzero : (guessedPosition splice).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch splice)
    (hchain : guessedChain selector = guessedChain splice) :
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice)
        0 1 (starts (guessedEpoch splice) (guessedChain splice))
      let out ← runContextFilteredSpliced hash enc K ctx adv pp selector splice answer starts
      return out.elim false
        (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)] {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x
      let out ← runContextFilteredSpliced hash enc K ctx adv pp selector splice answer starts
      return out.elim false
        (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)] {true} := by
  classical
  let : MeasurableSpace H := ⊤
  let F : H → (Epoch h → Fin v → H) → ProbComp Bool := fun answer starts =>
    (fun out => out.elim false
      (fun result =>
          observe result.pk result.sk.endpoints result.forgery result.history)) <$>
      runContextFilteredSpliced hash enc K ctx adv pp selector splice answer starts
  have hcouple := ReturnedMass.independent_coordinate_image_mass
    (GXMSS.sampleStarts H h v) sampleStarts_uniform_measure
    (guessedEpoch splice) (guessedChain splice)
    (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1) F
    (fun answer starts x => runContextFilteredSpliced_zero_start_update_mass
      hash enc K ctx adv pp selector splice answer starts x observe hzero hn hepoch hchain)
  simpa only [F, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    using hcouple
private theorem filteredZero_real_source_mass
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v)
    (hzero : (guessedPosition splice).val = 0) (hn : 0 < 2 ^ w - 1)
    (hepoch : guessedEpoch selector = guessedEpoch splice)
    (hchain : guessedChain selector = guessedChain splice) :
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice)
        0 1 (starts (guessedEpoch splice) (guessedChain splice))
      let out ← runFilteredSpliced hash enc K adv pp selector splice answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (selector, result))] {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1 x
      let out ← runFilteredSpliced hash enc K adv pp selector splice answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (selector, result))] {true} := by
  classical
  let : MeasurableSpace H := ⊤
  let F : H → (Epoch h → Fin v → H) → ProbComp Bool := fun answer starts =>
    (fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector splice answer starts
  have hcouple := ReturnedMass.independent_coordinate_image_mass
    (GXMSS.sampleStarts H h v) sampleStarts_uniform_measure
    (guessedEpoch splice) (guessedChain splice)
    (hash.chain pp (guessedEpoch splice) (guessedChain splice) 0 1) F
    (fun answer starts x => runFilteredSpliced_zero_start_update_mass
      hash enc K adv pp selector splice answer starts x hzero hn hepoch hchain)
  simpa only [F, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    using hcouple
/-- Advancing the filtered honest response from the first positive step to the selected cut
preserves the full adaptive filtered computation, including its absorbing abort state. -/
private theorem runContextFilteredSpliced_honest_from_zero
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector : Guess h w v) (starts : Epoch h → Fin v → H)
    (hn : 0 < 2 ^ w - 1) :
    runContextFilteredSpliced hash enc K ctx adv pp selector
      (guessedEpoch selector, guessedChain selector, ⟨0, hn⟩)
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0 1
        (starts (guessedEpoch selector) (guessedChain selector))) starts =
    runContextFilteredSpliced hash enc K ctx adv pp selector selector
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0
        ((guessedPosition selector).val + 1)
        (starts (guessedEpoch selector) (guessedChain selector))) starts := by
  let g := (guessedPosition selector).val
  let ep := guessedEpoch selector
  let i := guessedChain selector
  let start := starts ep i
  let splice (j : ℕ) (hj : j ≤ g) : Guess h w v :=
    (ep, i, ⟨j, lt_of_le_of_lt hj (guessedPosition selector).isLt⟩)
  have hiter : ∀ j (hj : j ≤ g),
      runContextFilteredSpliced hash enc K ctx adv pp selector (splice 0 (by omega))
        (hash.chain pp ep i 0 1 start) starts =
      runContextFilteredSpliced hash enc K ctx adv pp selector (splice j hj)
        (hash.chain pp ep i 0 (j + 1) start) starts := by
    intro j
    induction j with
    | zero =>
      intro hj
      rfl
    | succ j ih =>
      intro hj
      have hjprev : j ≤ g := by omega
      have hnext := runContextFilteredSpliced_advance hash enc K ctx adv pp selector
        (splice j hjprev) (splice (j + 1) hj)
        (hash.chain pp ep i 0 (j + 1) start) starts
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (by change (⟨j + 1, _⟩ : Fin (2 ^ w - 1)) ≤ guessedPosition selector
            exact Fin.le_iff_val_le_val.mpr hj)
      have hchain : hash.chain pp ep i (j + 1) 1
          (hash.chain pp ep i 0 (j + 1) start) =
          hash.chain pp ep i 0 (j + 1 + 1) start := by
        simpa only [Nat.zero_add] using
          (hash.chain_add pp ep i 0 (j + 1) 1 start).symm
      simp only [splice, guessedEpoch, guessedChain, guessedPosition] at hnext
      rw [hchain] at hnext
      simpa only [Nat.succ_eq_add_one] using (ih hjprev).trans hnext
  have hzero : splice 0 (by omega) =
      (ep, i, (⟨0, hn⟩ : Fin (2 ^ w - 1))) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  have hfinal : splice g (Nat.le_refl g) = selector := by
    rcases selector with ⟨⟨ep', i'⟩, pos⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        rfl
  simpa only [hzero, hfinal, ep, i, g, start] using hiter g (Nat.le_refl g)
/-- At an honest cut response, the full adaptive spliced interaction is the source interaction
with the same fixed keys and exactly the same optional signing law. -/
private theorem runSpliced_honest
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H) :
    runSpliced hash enc K adv pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts =
      runWithKeys hash enc K adv
        (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 := by
  unfold runSpliced runWithKeys
  rw [show splicedEndpoints hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts =
      GXMSS.endpoints hash pp starts from
        splicedEndpoints_honest hash pp guess starts]
  simp only [GXMSS.keys]
  rw [splicedSigningOracle_honest hash enc K pp guess starts]

/-- The complete filtered interaction specializes the deterministic context advance law. -/
private theorem runFilteredSpliced_honest_from_zero
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector : Guess h w v) (starts : Epoch h → Fin v → H)
    (hn : 0 < 2 ^ w - 1) :
    runFilteredSpliced hash enc K adv pp selector
      (guessedEpoch selector, guessedChain selector, ⟨0, hn⟩)
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0 1
        (starts (guessedEpoch selector) (guessedChain selector))) starts =
    runFilteredSpliced hash enc K adv pp selector selector
      (hash.chain pp (guessedEpoch selector) (guessedChain selector) 0
        ((guessedPosition selector).val + 1)
        (starts (guessedEpoch selector) (guessedChain selector))) starts := by
  exact runContextFilteredSpliced_honest_from_zero hash enc K (completeChainContext hash)
    adv pp selector starts hn

private def jointHonestSpliceProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let starts ← GXMSS.sampleStarts H h v
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
    ((guessedPosition guess).val + 1)
    (starts (guessedEpoch guess) (guessedChain guess))
  let out ← runSpliced hash enc K adv pp guess answer starts
  return jointChainObservation hash enc K (guess, out)
private theorem jointHonestSpliceProgram_eq_source
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointHonestSpliceProgram hash enc K adv =
      jointChainObservation hash enc K <$> gameFive hash enc K hv hw adv := by
  unfold jointHonestSpliceProgram gameFive sourceProgram GXMSS.keygen
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  apply bind_congr
  intro guess
  apply bind_congr
  intro pp
  apply bind_congr
  intro starts
  rw [runSpliced_honest hash enc K adv pp guess starts]
private def jointFilteredHonestProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let starts ← GXMSS.sampleStarts H h v
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
    ((guessedPosition guess).val + 1)
    (starts (guessedEpoch guess) (guessedChain guess))
  let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))
private def jointZeroRealProgram
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let guess ← $ᵗ (Guess h w v)
  let pp ← hash.thf.seedGen
  let x ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess,
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩)
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x
  let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))
private def jointZeroRealNormalized
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let guess ← $ᵗ (Guess h w v)
  let starts ← GXMSS.sampleStarts H h v
  let x ← ($ᵗ H : ProbComp H)
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess,
      ⟨0, Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))⟩)
  let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1 x
  let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
  return out.elim false
    (fun result => jointChainObservation hash enc K (guess, result))
private theorem jointZeroRealProgram_eq_normalized
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointZeroRealProgram hash enc K adv] =
      𝒟[jointZeroRealNormalized hash enc K adv] := by
  unfold jointZeroRealProgram jointZeroRealNormalized
  rw [OracleComp.evalDist_bind_bind_swap
    ($ᵗ (Guess h w v) : ProbComp (Guess h w v)) hash.thf.seedGen]
  apply evalDist_bind_congr
  intro pp
  apply evalDist_bind_congr
  intro guess
  exact OracleComp.evalDist_bind_bind_swap ($ᵗ H : ProbComp H)
    (GXMSS.sampleStarts H h v) _
/-- Filtering preserves the unconditioned selected source mass after all outer draws. -/
private theorem jointHonestSplice_mass_eq_filtered
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointHonestSpliceProgram hash enc K adv] {true} =
      𝒟[jointFilteredHonestProgram hash enc K adv] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  unfold jointHonestSpliceProgram jointFilteredHonestProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro starts
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    runSpliced_selectedMass_eq_filtered hash enc K adv pp guess guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts
/-- The filtered source mass equals the independently sampled real zero-cut hybrid. -/
private theorem jointFilteredHonest_mass_eq_zeroReal
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    𝒟[jointFilteredHonestProgram hash enc K adv] {true} =
      𝒟[jointZeroRealProgram hash enc K adv] {true} := by
  let : MeasurableSpace PP := ⊤
  let : MeasurableSpace H := ⊤
  let : MeasurableSpace (Epoch h → Fin v → H) := ⊤
  have hn : 0 < 2 ^ w - 1 := Nat.pos_of_ne_zero (NeZero.ne (2 ^ w - 1))
  unfold jointFilteredHonestProgram jointZeroRealProgram
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro guess
  apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
  intro pp
  let zero : Guess h w v :=
    (guessedEpoch guess, guessedChain guess, ⟨0, hn⟩)
  have hcut : 𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))
      let out ← runFilteredSpliced hash enc K adv pp guess guess answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (guess, result))] {true} =
    𝒟[do
      let starts ← GXMSS.sampleStarts H h v
      let answer := hash.chain pp (guessedEpoch guess) (guessedChain guess) 0 1
        (starts (guessedEpoch guess) (guessedChain guess))
      let out ← runFilteredSpliced hash enc K adv pp guess zero answer starts
      return out.elim false
        (fun result => jointChainObservation hash enc K (guess, result))] {true} := by
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro starts
    dsimp only
    rw [← runFilteredSpliced_honest_from_zero hash enc K adv pp guess starts hn]
  rw [hcut]
  simpa only [zero, guessedEpoch, guessedChain] using
    filteredZero_real_source_mass hash enc K adv pp guess zero rfl hn rfl rfl
/-- The exact source selected mass is the returned true mass of the real zero-cut hybrid. -/
private theorem jointChainAdvantage_eq_zeroReal
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    jointChainAdvantage hash enc K hv hw adv =
      𝒟[jointZeroRealProgram hash enc K adv] {true} := by
  unfold jointChainAdvantage jointChainOutputMeasure
  rw [ProbCompRuntime.probComp_evalDist,
    ← jointHonestSpliceProgram_eq_source hash enc K hv hw adv]
  exact (jointHonestSplice_mass_eq_filtered hash enc K adv).trans
    (jointFilteredHonest_mass_eq_zeroReal hash enc K adv)
/-- A finite additive telescope yields the desired loss from one Boolean UD distance. -/
private theorem finite_hybrid_boolDist_bound
    (source terminal real ideal distance : ℝ≥0∞) (n : ℕ)
    (hfinite : (n : ℝ≥0∞) * ideal ≠ ∞)
    (htelescope : source + (n : ℝ≥0∞) * ideal =
      terminal + (n : ℝ≥0∞) * real)
    (hdistance : real ≤ ideal + distance) :
    source ≤ terminal + (n : ℝ≥0∞) * distance := by
  exact HybridTelescope.finite_hybrid_boolDist_bound source terminal real ideal distance n
    hfinite htelescope hdistance

/-- Pointwise selected-cut masses average to the exact finite-prefix sum. -/
private theorem uniform_fin_prefix_true_mass_of_pointwise
    (n g : ℕ) [NeZero n] (hg : g ≤ n)
    (actual : Fin n → ProbComp Bool) (f : ℕ → ℝ≥0∞)
    (hpoint : ∀ j : Fin n,
      𝒟[actual j] {true} = if j.val < g then f j.val else 0) :
    𝒟[do let j ← ($ᵗ (Fin n) : ProbComp (Fin n)); actual j] {true} =
      (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, f j := by
  exact HybridTelescope.uniform_fin_prefix_true_mass_of_pointwise n g hg actual f hpoint

private theorem finite_chain_hybrid_mean_telescope (real ideal : ℕ → ℝ≥0∞)
    (n g : ℕ) [NeZero n]
    (htelescope : real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j) :
    real 0 + (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range g, ideal j) =
    real g + (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range g, real j) := by
  exact HybridTelescope.finite_chain_hybrid_mean_telescope real ideal n g htelescope

end GXMSS.Reductions
