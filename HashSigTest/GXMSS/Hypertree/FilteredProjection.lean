/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.FilteredSimulation
public import VCVio.OracleComp.Constructions.SampleableType.Measure
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Observations of absorbed signing simulations

Uniform requests can return different answers after rejection. The optional result/state
observation discards that suffix, while retaining its probability mass at `none`.
-/

public section

namespace GXMSS.Reductions.FilteredSimulation.Probe

open OracleComp OracleSpec

/-- Rejected simulations answer every later request with the canonical zero. -/
@[expose] def absorbing : QueryImpl unifSpec (StateT (Option Unit) ProbComp) :=
  fun n state => match state with
    | none => pure (0, none)
    | some _ => (fun answer => (answer, state)) <$> ($ᵗ (Fin (n + 1)))

/-- Uniform requests remain random after the signing state has been rejected. -/
@[expose] def sampling : QueryImpl unifSpec (StateT (Option Unit) ProbComp) :=
  fun n state => (fun answer => (answer, state)) <$> ($ᵗ (Fin (n + 1)))

/-- The complete optional observation preserves rejection mass despite different suffix answers. -/
theorem masked_run (program : OracleComp unifSpec (Fin 2)) (state : Option Unit) :
    (fun out => out.2.map (fun s => (out.1, s))) <$>
        (simulateQ absorbing program).run state =ᵈ
      (fun out => out.2.map (fun s => (out.1, s))) <$>
        (simulateQ sampling program).run state := by
  apply masked_simulateQ_run_evalDistEq
  · intro n out hout
    simp only [absorbing, StateT.run, mem_support_pure_iff] at hout
    exact congrArg Prod.snd hout
  · intro n out hout
    simp only [sampling, StateT.run, support_map, support_uniformSample, Set.mem_image,
      Set.mem_univ, true_and] at hout
    obtain ⟨_, rfl⟩ := hout
    rfl
  · intro n s
    exact EvalDistEq.refl _

/-- Raw returned outputs distinguish the two rejected simulations. -/
theorem raw_runs_differ :
    ¬ (simulateQ absorbing (liftM (OracleSpec.query (spec := unifSpec) 1) :
        OracleComp unifSpec (Fin 2))).run none =ᵈ
      (simulateQ sampling (liftM (OracleSpec.query (spec := unifSpec) 1) :
        OracleComp unifSpec (Fin 2))).run none := by
  intro h
  have hout : ((1 : Fin 2), (none : Option Unit)) ∈ support
      ((simulateQ absorbing (liftM (OracleSpec.query (spec := unifSpec) 1) :
        OracleComp unifSpec (Fin 2))).run none) := by
    rw [support_eq_of_evalDistEq h]
    simp [sampling, StateT.run]
  simp [absorbing, StateT.run] at hout

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``map_simulateQ_run_evalDistEq_of_query,
    ``masked_simulateQ_run_evalDistEq,
    ``masked_run,
    ``raw_runs_differ]

end GXMSS.Reductions.FilteredSimulation.Probe
