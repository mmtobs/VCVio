/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Shared ideal-cache and grouped-response controls

An odd chain count observes three cells of two complete pairs. The fourth cell remains an
unused response half. Counter retry families retain their one base query at budget zero.
-/

public section

namespace GXMSS.Hypertree.PRFDerived.Unforgeability.Probe

open OracleComp OracleSpec

/-- An odd three-chain component has two complete start response groups. -/
@[expose, reducible] def shape : Shape := ⟨2, 0, 1, 3, by decide⟩

/-- Altering only the unused final half does not alter any actual chain start. -/
theorem odd_unused_half (a b c unused other : Bool) :
    readPairs shape (fun group : Fin 2 => if group = 0 then (a, b) else (c, unused)) =
      readPairs shape (fun group : Fin 2 => if group = 0 then (a, b) else (c, other)) := by
  funext i
  fin_cases i <;> rfl

/-- Adjacent paired starts read the two halves of the same complete response. -/
theorem adjacent_halves (pairs : Fin 2 → Bool × Bool) :
    (readPairs shape pairs 0, readPairs shape pairs 1) = pairs 0 := by
  exact Prod.eta _

/-- A counter family with no attempted randomizer still derives its one base response. -/
theorem counter_zero_budget_query :
    responseFamilyQueries (Response := Bool) .pairedCounter 0 (fun _ : Unit => true) =
      (fun (response : Bool) (_ : Unit) => response) <$> PRFScheme.functionQuery true := rfl

/-- An IID family with no attempts has no response queries. -/
theorem iid_zero_budget_query :
    responseFamilyQueries (D := Bool) (Response := Bool) .iid 0 (fun i : Fin 0 => nomatch i) =
      pure Fin.elim0 := rfl

/-- Uniform individual halves do not imply a joint independent pair law. -/
theorem duplicated_pair_marginals :
    Prod.fst <$> ((fun b : Bool => (b, b)) <$> ($ᵗ Bool)) =ᵈ ($ᵗ Bool) ∧
      Prod.snd <$> ((fun b : Bool => (b, b)) <$> ($ᵗ Bool)) =ᵈ ($ᵗ Bool) := by
  constructor <;> (
    rw [Functor.map_map]
    change id <$> ($ᵗ Bool) =ᵈ ($ᵗ Bool)
    simpa only [id_map] using (EvalDistEq.refl ($ᵗ Bool)))

/-- A duplicated half lacks the full pair law required by the counter-layout constructor. -/
theorem duplicated_pair_not_joint :
    ¬ ((fun b : Bool => (b, b)) <$> ($ᵗ Bool)) =ᵈ ($ᵗ (Bool × Bool)) := by
  intro h
  have hbad : (false, true) ∈ support ((fun b : Bool => (b, b)) <$> ($ᵗ Bool)) := by
    rw [support_eq_of_evalDistEq h, support_uniformSample]
    trivial
  simp only [support_map, support_uniformSample, Set.mem_image,
    Set.mem_univ, true_and] at hbad
  obtain ⟨b, hb⟩ := hbad
  cases b <;> simp at hb

/-- An empty IID retry tape contributes no retry requests during eager setup. -/
theorem iid_zero_budget_eager_count :
    eagerQueryBound shape .iid (RetrySampling.iid (R := Bool) 0 0) 0 = 7 := by decide

/-- Empty counter traversals still derive every fixed base during eager setup. -/
theorem counter_zero_budget_eager_count :
    eagerQueryBound shape .pairedCounter
      (RetrySampling.counter 2 0 0 (by decide) (by decide)) 0 = 6 := by decide

section Consumer

variable {PP T X H M R Response Key : Type} {S : Shape}
    [SampleableType H] [SampleableType Response] [DecidableEq T] [DecidableEq X]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Hypertree.Signature R H S)]

example (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (qs : ℕ) (hv : 0 < S.v) (hw : 0 < S.w) (hnonmax : family.NoMaximumOutput)
    (adv : SchemeAdversary PP H M R S)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    SyncSignatureUnforgeability.advantage
      (PRFDerived.scheme hash family layout sampling prf interpretation retry)
      ProbCompRuntime.probComp adv ≤
        strongUnforgeabilityBound hash family layout sampling interpretation retry
          prf qs hv hw adv :=
  unforgeability_reduction_bound hash family layout sampling interpretation retry laws
    prf qs hv hw hnonmax adv hqueries

end Consumer

example := @SamplingLaws.iid
example := @SamplingLaws.counter
example := @paired_start_projection
example := @keyMaterialQueries_ideal
example := @keyMaterialQueries_retryFresh
example := @oracleSign_preserves_fresh
example := @oracleInteraction_ideal_eq_interaction
example := @randgenPRFReduction_query_bound
example := @randgenPRFReduction_real_strong
example := @randgenPRFReduction_ideal_strong
example := @adaptive_strong_additive_bound
example := @strong_unforgeability_reduction_bound
example := @unforgeability_reduction_bound

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``SamplingLaws.iid,
    ``SamplingLaws.counter,
    ``responseFamilyQueries_ideal_fresh,
    ``paired_start_projection,
    ``startQueries_ideal_fresh,
    ``internalCoinsQueries_ideal_fresh,
    ``keyMaterialQueries_ideal,
    ``keyMaterialQueries_retryFresh,
    ``oracleSign_preserves_fresh,
    ``oracleInteraction_ideal_eq_interaction,
    ``randgenPRFReduction_query_bound,
    ``randgenPRFReduction_real_strong,
    ``randgenPRFReduction_ideal_strong,
    ``adaptive_strong_additive_bound,
    ``strong_unforgeability_reduction_bound,
    ``unforgeability_reduction_bound]

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling,
      `HashSig.GXMSS.Security.Hypertree.Reductions.PRFDerivedOracleInteraction,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedQueryBounds,
      `HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability]
    #[(``SamplingLaws.iid, `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling),
      (``SamplingLaws.counter, `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling),
      (``paired_start_projection, `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling),
      (``oracleInteraction_ideal_eq_interaction,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling),
      (``randgenPRFReduction_real_strong,
        `HashSig.GXMSS.Security.Hypertree.Reductions.PRFDerivedOracleInteraction),
      (``randgenPRFReduction_query_bound,
        `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedQueryBounds),
      (``randgenPRFReduction_ideal_strong,
        `HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability),
      (``adaptive_strong_additive_bound,
        `HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability),
      (``strong_unforgeability_reduction_bound,
        `HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability),
      (``unforgeability_reduction_bound,
        `HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability)]
    #[]
    #[(``sampleResponseFamily, `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling),
      (``RetryFresh, `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling),
      (``randgenPRFReduction,
        `HashSig.GXMSS.Security.Hypertree.Reductions.PRFDerivedOracleInteraction),
      (``eagerQueryBound, `HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedQueryBounds),
      (``strongUnforgeabilityBound,
        `HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability)]

end GXMSS.Hypertree.PRFDerived.Unforgeability.Probe
