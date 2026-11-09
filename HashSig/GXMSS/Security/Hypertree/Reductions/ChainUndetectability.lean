/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainMass
import all HashSig.GXMSS.Security.Reductions.ChainUndetectability

/-!
# Global original-domain chain undetectability

One global selector and one chain-cut index determine a single challenge before seed reveal.
After reveal the named reduction runs the actual ancestor-aware filtered forest interaction.
Both challenge worlds use the common hash's original digest embedding.
-/

public section

namespace GXMSS.Hypertree.Security

open Encoding ENNReal OracleComp OracleSpec TweakableHash ChainContinuation ChainMass

variable {PP T X H M R : Type} {S : Shape}

/-- The one-target undetectability problem uses the original common input and digest embedding. -/
@[expose] noncomputable def chainUDProblem [SampleableType H]
    (hash : HashInstance PP T X H S) : SM_DT_UD_Problem Empty PP T X H H :=
  SM_DT_UD_Problem.standalone hash.thf hash.digestInput hash.digestInput.injective
    ($ᵗ H) ($ᵗ H) 1

/-- Private state prepared before the common hash seed is revealed. -/
structure UDState (H Coins : Type) (S : Shape) where
  /-- One selector over the complete forest chain-call domain. -/
  selector : ChainPosition S
  /-- One cut sampled from the complete positive-step domain. -/
  cut : Fin (2 ^ S.w - 1)
  /-- Full forest starts sampled independently of the challenge. -/
  starts : OTSPosition S → Fin S.v → H
  /-- Every fixed upper tape, including permanently failed certificates. -/
  upperCoins : UpperPosition S → Coins
  /-- The optional authoritative challenge response. -/
  answer : Option H

private noncomputable def udPick [SampleableType H] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (sampling : RetrySampling R)
    (hv : 0 < S.v) (hw : 0 < S.w) :
    OracleComp (unifSpec + (SM_DT_UD_challengeSpec T H +
      collectionSpec (chainUDProblem hash).thColl)) (UDState H sampling.internal.Coins S) := do
  let selector ← OracleComp.liftComp (sampleSelector S hv hw) _
  let cut ← OracleComp.liftComp ($ᵗ (Fin (2 ^ S.w - 1))) _
  let starts ← OracleComp.liftComp (sampleStarts S) _
  let upperCoins ← OracleComp.liftComp (sampleUpperCoins S sampling.sampleInternal) _
  let answer ← liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
    collectionSpec (chainUDProblem hash).thColl)).query
      (.inr (.inl (hash.chainTweak (selector.1, selector.2.1, cut)))))
  pure ⟨selector, cut, starts, upperCoins, answer⟩

/-- The named global reduction uses one original-domain challenge and the actual forest observer. -/
noncomputable def chainUndetectabilityReduction [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) :
    SM_DT_UD_Adversary (chainUDProblem hash) := by
  let : NeZero (2 ^ S.w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (Nat.ne_of_gt hw); omega⟩
  exact {
    State := UDState H sampling.internal.Coins S
    pick := udPick hash sampling hv hw
    distinguish := fun state pp =>
      if state.cut.val < state.selector.2.2.val then
        match state.answer with
        | none => pure false
        | some answer => runObserved hash family sampling adv pp state.selector.1
            state.selector.2.1 (state.selector.2.2.val + 1) state.cut.val answer
            state.starts state.upperCoins (observe pp state.selector)
      else pure false }

/-- The explicit authoritative challenge program retains all source draws and refused outcomes. -/
@[expose] noncomputable def explicitUDProgram [SampleableType H] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) (world : SM_DT_UD_World) :
    ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let selector ← sampleSelector S hv hw
  let cut ← ($ᵗ (Fin (2 ^ S.w - 1)) : ProbComp (Fin (2 ^ S.w - 1)))
  let starts ← sampleStarts S
  let upperCoins ← sampleUpperCoins S sampling.sampleInternal
  let answer ← SM_DT_UD_response world (chainUDProblem hash) pp
    (hash.chainTweak (selector.1, selector.2.1, cut))
  if cut.val < selector.2.2.val then
    runObserved hash family sampling adv pp selector.1 selector.2.1 (selector.2.2.val + 1)
      cut.val answer starts upperCoins (observe pp selector)
  else pure false

/-- Existing native lift semantics apply to the same original-domain problem in every component. -/
private theorem udOracles_liftComp [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H S) (world : SM_DT_UD_World) (pp : PP)
    {A : Type} (program : ProbComp A) (state : SM_DT_UD_State T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem hash) pp)
      (OracleComp.liftComp program _)).run state =
      (fun value => (value, state)) <$> program :=
  GXMSS.Reductions.jointUDOracles_liftComp (hash.componentHash (topTree S))
    world pp program state

/-- A single fresh native challenge has its authoritative response law. -/
private theorem udOracles_challenge [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H S) (world : SM_DT_UD_World) (pp : PP) (t : T) :
    (simulateQ (SM_DT_UD_oracles world (chainUDProblem hash) pp)
      (liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
        collectionSpec (chainUDProblem hash).thColl)).query (.inr (.inl t))))).run
        (([], []) : SM_DT_UD_State T) =
      (fun answer => (some answer, ([t], []))) <$>
        SM_DT_UD_response world (chainUDProblem hash) pp t :=
  GXMSS.Reductions.jointUDOracles_challenge (hash.componentHash (topTree S)) world pp t

/-- In either world the named native experiment equals its explicit full forest program. -/
theorem chainUndetectabilityReduction_experiment [SampleableType H] [DecidableEq T]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world
      (chainUndetectabilityReduction hash family sampling hv hw adv observe) =
      (letI : NeZero (2 ^ S.w - 1) :=
        ⟨by have := Nat.one_lt_two_pow (Nat.ne_of_gt hw); omega⟩
       explicitUDProgram hash family sampling hv hw adv observe world) := by
  unfold SM_DT_UD_Experiment chainUndetectabilityReduction udPick explicitUDProgram
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    pure_bind, bind_assoc]
  simp only [udOracles_liftComp, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  simp only [udOracles_challenge, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  rfl

/-- The real challenge is precisely one positive chain step at the globally selected tweak. -/
theorem ud_real_response_eq_chain [SampleableType H]
    (hash : HashInstance PP T X H S) (pp : PP) (p : OTSPosition S) (i : Fin S.v)
    (cut : Fin (2 ^ S.w - 1)) :
    SM_DT_UD_response .real (chainUDProblem hash) pp (hash.chainTweak (p, i, cut)) =
      (fun x => (chainFamily hash pp).chain p i cut.val 1 x) <$> ($ᵗ H : ProbComp H) := by
  exact GXMSS.Reductions.jointUD_real_response_eq_chain (hash.componentHash p.1) pp p.2 i cut

/-- The ideal challenge is the original uniformly sampled digest domain. -/
theorem ud_ideal_response_eq_uniform [SampleableType H]
    (hash : HashInstance PP T X H S) (pp : PP) (p : OTSPosition S) (i : Fin S.v)
    (cut : Fin (2 ^ S.w - 1)) :
    SM_DT_UD_response .ideal (chainUDProblem hash) pp (hash.chainTweak (p, i, cut)) =
      ($ᵗ H : ProbComp H) := rfl

/-- The actual uniformly selected cut experiment, with inactive indices observed as false. -/
@[expose] noncomputable def selectedCutProgram [SampleableType H] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) (world : SM_DT_UD_World) :
    ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let selector ← sampleSelector S hv hw
  let cut ← ($ᵗ (Fin (2 ^ S.w - 1)) : ProbComp (Fin (2 ^ S.w - 1)))
  if cut.val < selector.2.2.val then
    filteredCutProgram hash family sampling adv pp selector.1 selector.2.1 selector.2.2.val
      cut.val world (observe pp selector)
  else pure false

/-- Native challenge draws give the actual cut program in both worlds, including inactive cuts. -/
theorem explicitUDProgram_evalDistEq_selectedCut [SampleableType H] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) (world : SM_DT_UD_World) :
    explicitUDProgram hash family sampling hv hw adv observe world =ᵈ
      selectedCutProgram hash family sampling hv hw adv observe world := by
  unfold explicitUDProgram selectedCutProgram
  apply EvalDistEq.bind_right
  intro pp
  apply EvalDistEq.bind_right
  intro selector
  apply EvalDistEq.bind_right
  intro cut
  by_cases hactive : cut.val < selector.2.2.val
  · apply EvalDistEq.of_evalDist_eq
    apply congrArg (fun program : ProbComp Bool => 𝒟[program])
    simp only [hactive, ↓reduceIte]
    unfold filteredCutProgram
    apply bind_congr
    intro starts
    apply bind_congr
    intro upperCoins
    cases world with
    | real =>
        rw [ud_real_response_eq_chain]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    | ideal => rfl
  · apply EvalDistEq.of_evalDist_eq
    simp only [hactive, ↓reduceIte]
    simp only [OracleComp.evalDist_bind_const]

/-- Both native UD world measures are the actual selected full-forest cut measures. -/
theorem chainUndetectabilityReduction_evalDistEq_selectedCut
    [SampleableType H] [DecidableEq T] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world
      (chainUndetectabilityReduction hash family sampling hv hw adv observe) =ᵈ
      selectedCutProgram hash family sampling hv hw adv observe world := by
  rw [chainUndetectabilityReduction_experiment]
  exact explicitUDProgram_evalDistEq_selectedCut hash family sampling hv hw adv observe world

/-- Initial real cuts with one global selector and the source seed distribution. -/
@[expose] noncomputable def cutSourceProgram [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let selector ← sampleSelector S hv hw
  filteredCutProgram hash family sampling adv pp selector.1 selector.2.1 selector.2.2.val 0
    .real (observe pp selector)

/-- Terminal real cuts retain the selected coordinate's actual cut rather than a component guess. -/
@[expose] noncomputable def cutTerminalProgram [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) : ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let selector ← sampleSelector S hv hw
  filteredCutProgram hash family sampling adv pp selector.1 selector.2.1 selector.2.2.val
    selector.2.2.val .real (observe pp selector)

/-- Integrating the concrete fixed-selector telescopes preserves the sharp common cut factor. -/
theorem global_cut_telescope [SampleableType H] [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) :
    𝒟[cutSourceProgram hash family sampling hv hw adv observe] {true} +
        ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[selectedCutProgram hash family sampling hv hw adv observe .ideal] {true} =
      𝒟[cutTerminalProgram hash family sampling hv hw adv observe] {true} +
        ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) *
          𝒟[selectedCutProgram hash family sampling hv hw adv observe .real] {true} := by
  let : MeasurableSpace (PP × ChainPosition S) := ⊤
  let draw : ProbComp (PP × ChainPosition S) := do
    let pp ← hash.thf.seedGen
    let selector ← sampleSelector S hv hw
    pure (pp, selector)
  have h := GXMSS.Reductions.HybridTelescope.bind_true_mass_telescope draw
    (fun z => filteredCutProgram hash family sampling adv z.1 z.2.1 z.2.2.1 z.2.2.2.val 0
      .real (observe z.1 z.2))
    (fun z => do
      let cut ← ($ᵗ (Fin (2 ^ S.w - 1)) : ProbComp (Fin (2 ^ S.w - 1)))
      if cut.val < z.2.2.2.val then
        filteredCutProgram hash family sampling adv z.1 z.2.1 z.2.2.1 z.2.2.2.val cut.val
          .ideal (observe z.1 z.2)
      else pure false)
    (fun z => filteredCutProgram hash family sampling adv z.1 z.2.1 z.2.2.1 z.2.2.2.val
      z.2.2.2.val .real (observe z.1 z.2))
    (fun z => do
      let cut ← ($ᵗ (Fin (2 ^ S.w - 1)) : ProbComp (Fin (2 ^ S.w - 1)))
      if cut.val < z.2.2.2.val then
        filteredCutProgram hash family sampling adv z.1 z.2.1 z.2.2.1 z.2.2.2.val cut.val
          .real (observe z.1 z.2)
      else pure false)
    (2 ^ S.w - 1)
    (fun z => filteredCutProgram_telescope hash family sampling adv z.1 z.2.1 z.2.2.1
      z.2.2.2.val (observe z.1 z.2) z.2.2.2.isLt)
  simpa only [draw, cutSourceProgram, cutTerminalProgram, selectedCutProgram, bind_assoc,
    pure_bind] using h

/-- The named original-domain UD advantage bounds the actual global cut telescope loss. -/
theorem cutSource_mass_le_terminal_add_UD [SampleableType H] [DecidableEq T]
    [NeZero (2 ^ S.w - 1)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (hv : 0 < S.v) (hw : 0 < S.w)
    (adv : SchemeAdversary PP H M R S)
    (observe : PP → ChainPosition S → Observation M H R S) :
    𝒟[cutSourceProgram hash family sampling hv hw adv observe] {true} ≤
      𝒟[cutTerminalProgram hash family sampling hv hw adv observe] {true} +
        ((2 ^ S.w - 1 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage
            (chainUndetectabilityReduction hash family sampling hv hw adv observe) := by
  let real := selectedCutProgram hash family sampling hv hw adv observe .real
  let ideal := selectedCutProgram hash family sampling hv hw adv observe .ideal
  let reduction := chainUndetectabilityReduction hash family sampling hv hw adv observe
  have hreal : 𝒟[SM_DT_UD_Experiment .real reduction] = 𝒟[real] :=
    chainUndetectabilityReduction_evalDistEq_selectedCut
      hash family sampling hv hw adv observe .real |>.evalDist_eq
  have hideal : 𝒟[SM_DT_UD_Experiment .ideal reduction] = 𝒟[ideal] :=
    chainUndetectabilityReduction_evalDistEq_selectedCut
      hash family sampling hv hw adv observe .ideal |>.evalDist_eq
  have hdist : 𝒟[real] {true} ≤ 𝒟[ideal] {true} + SM_DT_UD_Advantage reduction := by
    have h := MeasureTheory.Measure.apply_true_le_add_boolDist
      𝒟[SM_DT_UD_Experiment .real reduction] 𝒟[SM_DT_UD_Experiment .ideal reduction]
    simpa only [SM_DT_UD_Advantage, hreal, hideal] using h
  apply GXMSS.Reductions.HybridTelescope.finite_hybrid_boolDist_bound _ _ _ _ _
    (2 ^ S.w - 1) _ (global_cut_telescope hash family sampling hv hw adv observe) hdist
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (evalDist_apply_le_one ideal {true}))

end GXMSS.Hypertree.Security
