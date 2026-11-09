/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.ChainContinuation
public import HashSig.GXMSS.Security.Auxiliary.FilteredSimulation
public import HashSig.GXMSS.Security.Auxiliary.ReturnedMass
public import HashSig.GXMSS.Security.Auxiliary.HybridTelescope
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainMass
public import HashSig.GXMSS.Security.Hypertree.Unforgeability
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Chain continuation consumers

Three OTS coordinates exercise endpoint-derived ancestor metadata, fixed failed certificates,
safe selected-prefix reads, untouched zero-position reads, and exact finite-selector masses.
The fixture imports the common public kernels without private implementation access.
-/

public section

namespace GXMSS.Hypertree.ChainContinuationTests
open ENNReal OracleComp OracleSpec
open GXMSS.Reductions
open ChainContinuation

/-- A nonconstant chain family over three global OTS coordinates. -/
private def family : ChainFamily (Fin 3) ℕ 1 where
  chain := fun _ _ _ count start => start + count
  chain_zero := by intros; omega
  chain_add := by intros; omega

/-- Distinct starts at the three coordinates. -/
private def starts (c : Fin 3) (_ : Fin 1) : ℕ := c.val

/-- Parent-message metadata and an optional fixed certificate, with two prefix reads. -/
private def continuation :
    EndpointContinuation (Fin 3) ℕ Bool (ℕ × Option ℕ) ((ℕ × Option ℕ) × ℕ × ℕ) 1 where
  prepare := fun ends coin =>
    let message := ends 0 0 + 2 * ends 1 0
    (message, if coin then some (message + 1) else none)
  materialize := fun metadata prefixes => (metadata, prefixes 0 0 2, prefixes 2 0 0)
  reads := fun _ c _ p => (c = 0 ∧ p = 2) ∨ (c = 2 ∧ p = 0)
  materialize_congr := by
    intro metadata left right hread
    rw [hread 0 0 2 (Or.inl ⟨rfl, rfl⟩), hread 2 0 0 (Or.inr ⟨rfl, rfl⟩)]

/-- Equal endpoint tables preserve all metadata, including an exhausted fixed certificate. -/
private theorem fixed_failure_advance (answer : ℕ) (coin : Bool) :
    continuation.materialize
      (continuation.prepare (spliceEndpoints family 3 0 0 0 answer starts) coin)
      (spliceValue family 0 0 0 answer starts) =
    continuation.materialize
      (continuation.prepare (spliceEndpoints family 3 0 0 1 (answer + 1) starts) coin)
      (spliceValue family 0 0 1 (answer + 1) starts) := by
  apply continuation.materialize_splice_advance family 3 0 0 0 answer starts coin (by omega)
  intro c i p hread hc _
  rcases hread with ⟨_, hp⟩ | ⟨hc', _⟩
  · omega
  · have : (0 : Fin 3) = 2 := hc.symm.trans hc'
    contradiction

/-- Zero-cut independence permits zero-position reads at an untouched coordinate. -/
private theorem old_start_unused (answer replacement : ℕ) (coin : Bool) :
    continuation.materialize
      (continuation.prepare
        (spliceEndpoints family 3 0 0 0 answer
          (Function.update starts 0 (Function.update (starts 0) 0 replacement))) coin)
      (spliceValue family 0 0 0 answer
        (Function.update starts 0 (Function.update (starts 0) 0 replacement))) =
    continuation.materialize
      (continuation.prepare (spliceEndpoints family 3 0 0 0 answer starts) coin)
      (spliceValue family 0 0 0 answer starts) := by
  apply continuation.materialize_zero_start_update family 3 0 0 answer starts replacement
    coin (by omega)
  intro c i p hread hc _
  rcases hread with ⟨_, hp⟩ | ⟨hc', _⟩
  · omega
  · have : (0 : Fin 3) = 2 := hc.symm.trans hc'
    contradiction

/-- Changed child endpoints require recomputing parent messages even when certificates fail. -/
private theorem changed_ancestor_message :
    continuation.prepare (spliceEndpoints family 3 0 0 0 7 starts) false ≠
      continuation.prepare
        (GXMSS.Reductions.ChainContinuation.endpoints family 3 starts) false := by
  decide

/-- A fixed exhausted certificate remains a returned failure under every splice. -/
private theorem failed_certificate (answer : ℕ) :
    (continuation.prepare (spliceEndpoints family 3 0 0 0 answer starts) false).2 = none := rfl

/-- The old selected start is observable at position zero, so safe-read premises are necessary. -/
private theorem unsafe_zero_read :
    spliceValue family 0 0 0 7 starts 0 0 0 ≠
      spliceValue family 0 0 0 7
        (Function.update starts 0 (Function.update (starts 0) 0 99)) 0 0 0 := by
  decide

/-- An honest response recovers endpoints even for the zero-length boundary. -/
private theorem zero_length_honest :
    spliceEndpoints family 0 0 0 0 (family.chain 0 0 0 1 (starts 0 0)) starts =
      GXMSS.Reductions.ChainContinuation.endpoints family 0 starts :=
  spliceEndpoints_honest family 0 0 0 0 starts

/-- One global selector pays only its six actual coordinates. -/
theorem selector_mass :
    Pr{let i ← ($ᵗ (Fin 6) : ProbComp (Fin 6))}[decide (i = 3) = true] =
      (6 : ℝ≥0∞)⁻¹ := by
  apply ReturnedMass.uniform_selector_probability true
    (fun i : Fin 6 => decide (i = 3))
  · intro _
    exact ⟨3, fun _ => by simp⟩
  · intros; rfl

/-- Unused hybrid indices return false and contribute no selected winning mass. -/
theorem unused_hybrid_coordinates :
    𝒟[do
      let i ← ($ᵗ (Fin 3) : ProbComp (Fin 3))
      pure (decide (i.val < 1))] {true} = (3 : ℝ≥0∞)⁻¹ := by
  have h := HybridTelescope.uniform_fin_prefix_true_mass_of_pointwise 3 1 (by omega)
    (fun i : Fin 3 => pure (decide (i.val < 1))) (fun _ => 1) (by
      intro i
      by_cases hi : i.val < 1 <;> simp [hi])
  simpa using h

/-- Returned false remains distinct from optional failure before observation. -/
theorem optional_failure_observation :
    𝒟[(fun answer : Option Bool => answer.elim false id) <$>
      (pure none : ProbComp (Option Bool))] {true} = 0 := by
  simp

/-- A selected first response is independent of its unused old coordinate after refresh. -/
theorem independent_first_response :
    𝒟[do
      let table ← ($ᵗ (Fin 3 → Fin 1 → Bool) : ProbComp (Fin 3 → Fin 1 → Bool))
      pure (table 0 0 && table 2 0)] {true} =
    𝒟[do
      let answer ← ($ᵗ Bool : ProbComp Bool)
      let table ← ($ᵗ (Fin 3 → Fin 1 → Bool) : ProbComp (Fin 3 → Fin 1 → Bool))
      pure (answer && table 2 0)] {true} := by
  apply ReturnedMass.independent_coordinate_image_mass
    ($ᵗ (Fin 3 → Fin 1 → Bool)) SampleableType.evalDist_uniformSample 0 0 id
    (fun answer table => pure (answer && table 2 0))
  intro answer table x
  simp [Function.update, show (2 : Fin 3) ≠ 0 by decide]

/-- The exact telescope keeps the unused third cut in the sampling domain. -/
theorem returned_telescope (program : ℕ → ProbComp Bool) :
    𝒟[program 0] {true} + (3 : ℝ≥0∞) * 𝒟[do
      let j ← ($ᵗ (Fin 3) : ProbComp (Fin 3))
      if j.val < 2 then program (j.val + 1) else pure false] {true} =
    𝒟[program 2] {true} + (3 : ℝ≥0∞) * 𝒟[do
      let j ← ($ᵗ (Fin 3) : ProbComp (Fin 3))
      if j.val < 2 then program j.val else pure false] {true} := by
  exact HybridTelescope.uniform_prefix_true_mass_telescope program (fun j => program (j + 1))
    3 2 (by omega) (fun _ _ => rfl)

/-- Each request can irreversibly mark the original state as bad. -/
private def querySpec : OracleSpec Bool := fun _ => Unit

private def original : QueryImpl querySpec (StateT Bool ProbComp) :=
  fun request state => pure ((), state || request)

private def filtered : QueryImpl querySpec (StateT (Option Bool) ProbComp) :=
  fun request state => match state with
    | none => pure ((), none)
    | some first => pure ((), if first || request then none else some false)

/-- Absorbing filtering preserves each good returned output of the full adaptive program. -/
private theorem adaptive_good_output (program : OracleComp querySpec Unit) :
    𝒟[(simulateQ original program).run false] {((), false)} =
      𝒟[(simulateQ filtered program).run (some false)] {((), some false)} := by
  apply FilteredSimulation.goodOutput_simulateQ_eq_filtered original filtered id
    (fun _ _ => ()) ?_ ?_ ?_ ?_ program false () false rfl
  · intro t u s _
    cases u
    rfl
  · intro t s hs z hz
    have hs' : s = true := hs
    subst s
    change z ∈ support (pure ((), true || t) : ProbComp (Unit × Bool)) at hz
    have hret : z = ((), true || t) := OracleComp.eq_of_mem_support_pure _ hz
    have hz' : z = ((), true) := by simpa only [Bool.true_or] using hret
    rw [hz']
    rfl
  · intro t z hz
    change z ∈ support (pure ((), none) : ProbComp (Unit × Option Bool)) at hz
    have hz' : z = ((), none) := OracleComp.eq_of_mem_support_pure _ hz
    rw [hz']
  · intro t s hs
    have hs' : s = false := hs
    subst s
    change (fun z : Unit × Bool => ((), if z.2 then none else some z.2)) <$>
        (pure ((), false || t) : ProbComp (Unit × Bool)) =
      pure ((), if false || t then none else some false)
    cases t <;> simp

end GXMSS.Hypertree.ChainContinuationTests

namespace GXMSS.Hypertree.ForestContinuationTests
open Encoding _root_.GXMSS.Hypertree.Security

/-- Two one-leaf layers isolate permanent internal exhaustion from bottom retry success. -/
private abbrev shape : Shape := ⟨2, 0, 1, 1, by decide⟩

private def word : Codeword 1 2 := fun _ => 0

private def encoding : IncomparableEncoding Unit Bool Bool Unit 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    have hx' : x = word := hx
    have hy' : y = word := hy
    exact False.elim (hne (hx'.trans hy'.symm))
  encode _ _ r _ := if r then some ⟨word, rfl⟩ else none

private def family : EncodingFamily Unit Bool Bool Bool shape where
  component _ := by simpa [Message, shape] using encoding

private def sampling : RetrySampling Bool where
  bottom := RetryPlan.iid Bool 1
  internal := RetryPlan.iid Bool 0
  sampleBottom := pure (fun _ => true)
  sampleInternal := pure Fin.elim0

private def metadata {T X : Type} (hash : HashInstance Unit T X Bool shape) :
    ChainContinuation.Metadata Bool Bool shape :=
  ChainContinuation.prepare hash family sampling.internal () (fun _ _ => false)
    (fun _ => Fin.elim0)

/-- Successful bottom retries do not reveal any prefixes after permanent internal exhaustion. -/
private theorem failed_internal_drops_prefixes {T X : Type}
    (hash : HashInstance Unit T X Bool shape)
    (prefixes : OTSPosition shape → Fin shape.v → ℕ → Bool) :
    ChainContinuation.materialize family sampling () 0 true (fun _ => true)
      (metadata hash) prefixes = none := by
  unfold ChainContinuation.materialize
  cases h : (ChainContinuation.bottomResult family sampling.bottom () 0 true
    (fun _ => true)).output <;> rfl

/-- The actual disclosed-read guard keeps a successful bottom retry whose full answer fails. -/
private theorem failed_consumed_is_not_disclosed {T X : Type}
    (hash : HashInstance Unit T X Bool shape) :
    ChainMass.disclosedBad (metadata hash) (bottomPosition shape 0) 0 1
      ⟨0, true, .success word true 1 [true]⟩ = false := rfl

/-- Full certificate failure still leaves the successful bottom word as the private reference. -/
private theorem failed_full_bottom_reference_retained {T X : Type}
    (hash : HashInstance Unit T X Bool shape) :
    Security.referenceResult (metadata hash)
      (SyncSignatureUnforgeability.emptyHistory, [⟨0, true, .success word true 1 [true]⟩])
      (bottomPosition shape 0) = some (word, true) := by
  exact Security.referenceResult_bottom_of_mem (metadata hash)
    (SyncSignatureUnforgeability.emptyHistory, [⟨0, true, .success word true 1 [true]⟩])
    (by simp) ⟨0, true, .success word true 1 [true]⟩ (by simp)

/-- The actual optional signing materializer has no safe-read obligations on this failed call. -/
private theorem failed_reads_empty {T X : Type} (hash : HashInstance Unit T X Bool shape)
    (p : OTSPosition shape) (i : Fin shape.v) (position : ℕ) :
    ¬ChainContinuation.Reads family sampling () 0 true (fun _ => true)
      (metadata hash) p i position := by
  intro hread
  have hsuccess := hread.1
  change (ChainContinuation.wordsFromResult (metadata hash) 0
    (ChainContinuation.bottomResult family sampling.bottom () 0 true (fun _ => true))).isSome =
      true at hsuccess
  unfold ChainContinuation.wordsFromResult at hsuccess
  cases hout : (ChainContinuation.bottomResult family sampling.bottom () 0 true
    (fun _ => true)).output with
  | none =>
      rw [hout] at hsuccess
      exact Bool.false_ne_true hsuccess
  | some wr =>
      rw [hout] at hsuccess
      exact Bool.false_ne_true hsuccess

end GXMSS.Hypertree.ForestContinuationTests

meta section

run_cmd Lean.Elab.Command.liftTermElabM do
  let chain := `HashSig.GXMSS.Security.Auxiliary.ChainContinuation
  let filtered := `HashSig.GXMSS.Security.Auxiliary.FilteredSimulation
  let mass := `HashSig.GXMSS.Security.Auxiliary.ReturnedMass
  let telescope := `HashSig.GXMSS.Security.Auxiliary.HybridTelescope
  let splicing := `HashSig.GXMSS.Security.Auxiliary.ChainSplicing
  let source := `HashSig.GXMSS.Security.Auxiliary.ChainSourceMass
  let selected := `HashSig.GXMSS.Security.Auxiliary.ChainTelescope
  let forest := `HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainContinuation
  let forestMass := `HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainMass
  let forestUD := `HashSig.GXMSS.Security.Hypertree.Reductions.ChainUndetectability
  let forestPRE := `HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
  let final := `HashSig.GXMSS.Security.Hypertree.Unforgeability
  let singleChain := `HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames
  let endpoints := #[
    (`GXMSS.Reductions.ChainContinuation.spliceValue_honest, chain),
    (`GXMSS.Reductions.ChainContinuation.spliceEndpoints_advance, chain),
    (`GXMSS.Reductions.ChainContinuation.EndpointContinuation.materialize_splice_advance, chain),
    (`GXMSS.Reductions.ChainContinuation.EndpointContinuation.materialize_zero_start_update, chain),
    (`GXMSS.Reductions.FilteredSimulation.goodOutput_simulateQ_eq_filtered, filtered),
    (`GXMSS.Reductions.FilteredSimulation.goodEvent_eq_filtered, filtered),
    (`GXMSS.Reductions.ReturnedMass.independent_coordinate_image_mass, mass),
    (`GXMSS.Reductions.ReturnedMass.uniform_selector_probability, mass),
    (`GXMSS.Reductions.HybridTelescope.uniform_prefix_true_mass_telescope, telescope),
    (`GXMSS.Reductions.jointChainGuess_probability, source),
    (`GXMSS.Reductions.jointChainAdvantage_eq_gameFourAdvantage_div_guess_card, selected),
    (`GXMSS.Hypertree.Security.ChainContinuation.materialize_honest, forest),
    (`GXMSS.Hypertree.Security.ChainContinuation.selected_internal_message_locality, forest),
    (`GXMSS.Hypertree.Security.ChainMass.filtered_good_raw_output, forestMass),
    (`GXMSS.Hypertree.Security.ChainMass.runFilteredRaw_advance, forestMass),
    (`GXMSS.Hypertree.Security.ChainMass.runFilteredRaw_zero_start_update, forestMass),
    (`GXMSS.Hypertree.Security.ChainMass.guarded_unfiltered_mass_le_observed, forestMass),
    (`GXMSS.Hypertree.Security.chainUndetectabilityReduction_experiment, forestUD),
    (`GXMSS.Hypertree.Security.chainUndetectabilityReduction_evalDistEq_selectedCut, forestUD),
    (`GXMSS.Hypertree.Security.chainPreimageReduction_experiment, forestPRE),
    (`GXMSS.Hypertree.Security.sourceResidual_mass_le_chain, forestPRE),
    (`GXMSS.Hypertree.Unforgeability.strong_unforgeability_reduction_bound, final),
    (`GXMSS.Hypertree.Unforgeability.unforgeability_reduction_bound, final),
    (`GXMSS.Hypertree.SingleLayer.chainUD_response_single, singleChain),
    (`GXMSS.Hypertree.SingleLayer.cutValidityGuard_single, singleChain)]
  GXMSS.Test.TrustAudit.check
    #[chain, filtered, mass, telescope, splicing, source, selected, forest, forestMass,
      forestUD, forestPRE, final, singleChain]
    endpoints #[] #[
      (`GXMSS.Reductions.ChainContinuation.spliceValue, chain),
      (`GXMSS.Reductions.ChainContinuation.spliceEndpoints, chain),
      (`GXMSS.Hypertree.Unforgeability.strongUnforgeabilityBound, final)]
