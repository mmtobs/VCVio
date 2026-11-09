/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.PRFDerivedScheme
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
public import VCVio.EvalDist.IndepProductMeasure

/-!
# Local sampling and shared-oracle hypertree preparation

Setup requests use the actual layout domain and retain one signing core. IID setup requests one
response per start; paired setup requests one complete response per start group. All internal
retry tapes are fixed once before adaptive signing. Duplicate global requests are rejected
before any fresh retry request. The ideal PRF interpreter retains one complete-response cache
through setup and all signing calls.
-/

public section

namespace GXMSS.Hypertree.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.SigningSimulation

variable {PP T X H M R Response Key : Type} {S : Shape}

/-- Actual shared function request domain for captured per-kind budgets. -/
abbrev Domain (PP M H R : Type) (S : Shape) (layout : Layout) (sampling : RetrySampling R) :=
  Query PP M H S layout (retryBudget sampling)

/-- Query the exact finite response family used by a retry layout. -/
@[expose] def responseFamilyQueries {D : Type} (layout : Layout) (budget : ℕ)
    (input : RetryIndex layout budget → D) :
    OracleComp (PRFScheme.PRFOracleSpec D Response) (RetryIndex layout budget → Response) :=
  match layout with
  | .iid => Fin.mOfFn budget fun i => PRFScheme.functionQuery (input i)
  | .pairedCounter => (fun response _ => response) <$> PRFScheme.functionQuery (input ())

/-- The local response-tape distribution of one retry family. A counter family contains one
complete response, even when its finite retry budget is zero. -/
@[expose] def sampleResponseFamily (Response : Type) [SampleableType Response]
    (layout : Layout) (budget : ℕ) : ProbComp (RetryIndex layout budget → Response) :=
  match layout with
  | .iid => Fin.mOfFn budget fun _ => $ᵗ Response
  | .pairedCounter => (fun response _ => response) <$> ($ᵗ Response)

/-- Local full-response projection laws. They describe seed, start and finite retry-coin sampling;
no signing interaction or security experiment correspondence is a field. -/
structure SamplingLaws [SampleableType Response] [SampleableType H]
    (hash : HashInstance PP T X H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) : Prop where
  /-- The distinguished response has the actual public-parameter distribution. -/
  publicParameter : interpretation.publicParameter <$> ($ᵗ Response) =ᵈ hash.thf.seedGen
  /-- Grouped starts require a joint pair law, including the half unused by an odd chain count. -/
  starts : match layout with
    | .iid => interpretation.chainStart <$> ($ᵗ Response) =ᵈ ($ᵗ H)
    | .pairedCounter => interpretation.chainPair <$> ($ᵗ Response) =ᵈ
        (do let left ← ($ᵗ H); let right ← ($ᵗ H); pure (left, right))
  /-- The complete bottom retry coin decoder has its captured local coin distribution. -/
  bottomCoins : retry.bottomCoins <$>
      sampleResponseFamily Response layout sampling.bottom.budget =ᵈ sampling.sampleBottom
  /-- The complete internal retry coin decoder has its captured local coin distribution. -/
  internalCoins : retry.internalCoins <$>
      sampleResponseFamily Response layout sampling.internal.budget =ᵈ sampling.sampleInternal

/-- Fresh distinct inputs produce the actual local response-family distribution. -/
theorem responseFamilyQueries_ideal_fresh {D : Type} [DecidableEq D] [SampleableType Response]
    (layout : Layout) (budget : ℕ) (input : RetryIndex layout budget → D)
    (hinj : Function.Injective input) (cache : (D →ₒ Response).QueryCache)
    (hfresh : ∀ i, cache (input i) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
      (responseFamilyQueries layout budget input)).run' cache =
        sampleResponseFamily Response layout budget := by
  cases layout with
  | iid => exact ideal_fin_queries_fresh budget input hinj cache hfresh
  | pairedCounter =>
    simp only [responseFamilyQueries, sampleResponseFamily, simulateQ_map, state_run'_map]
    rw [PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery]
    unfold OracleSpec.randomOracle
    rw [StateT.run'_eq, QueryImpl.withCaching_run_none _ (hfresh ())]
    simp [map_eq_bind_pure_comp, bind_assoc]

/-- Coordinatewise equal-in-distribution draws retain the complete finite product law. -/
theorem mOfFn_evalDistEq {A : Type} (n : ℕ) (left : Fin n → ProbComp A)
    (right : Fin n → ProbComp A) (h : ∀ i, left i =ᵈ right i) :
    Fin.mOfFn n left =ᵈ Fin.mOfFn n right := by
  induction n with
  | zero => exact EvalDistEq.refl _
  | succ n ih =>
    simp only [Fin.mOfFn]
    apply (h 0).bind_congr
    intro first
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      (ih (fun i => left i.succ) (fun i => right i.succ) (fun i => h i.succ)).map
        (fun rest : Fin n → A => (Fin.cons first rest : Fin (n + 1) → A))

/-- IID finite response projection supplies the canonical complete randomizer-tuple law. -/
theorem iid_coin_projection [SampleableType Response] [SampleableType R]
    (project : Response → R) (hlaw : project <$> ($ᵗ Response) =ᵈ ($ᵗ R)) (budget : ℕ) :
    (fun responses : Fin budget → Response => fun i => project (responses i)) <$>
        sampleResponseFamily Response .iid budget =ᵈ ($ᵗ (Fin budget → R)) := by
  rw [sampleResponseFamily, Fin.mOfFn_map]
  have htuple := mOfFn_evalDistEq budget (fun _ => project <$> ($ᵗ Response))
    (fun _ => ($ᵗ R)) (fun _ => hlaw)
  refine htuple.trans ?_
  let : MeasurableSpace R := ⊤
  apply EvalDistEq.of_evalDist_eq
  rw [evalDist_mOfFn, RetryPlan.evalDist_iid_coins]

/-- Local IID laws follow from the actual single-response seed, start and randomizer projections. -/
theorem SamplingLaws.iid [SampleableType Response] [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H S) (interpretation : Interpretation PP H R Response)
    (bottomBudget internalBudget : ℕ)
    (hseed : interpretation.publicParameter <$> ($ᵗ Response) =ᵈ hash.thf.seedGen)
    (hstart : interpretation.chainStart <$> ($ᵗ Response) =ᵈ ($ᵗ H))
    (hrandomizer : interpretation.retryRandomizer <$> ($ᵗ Response) =ᵈ ($ᵗ R)) :
    SamplingLaws hash .iid (RetrySampling.iid (R := R) bottomBudget internalBudget) interpretation
      (RetryInterpretation.iid bottomBudget internalBudget interpretation) where
  publicParameter := hseed
  starts := hstart
  bottomCoins := iid_coin_projection interpretation.retryRandomizer hrandomizer bottomBudget
  internalCoins := iid_coin_projection interpretation.retryRandomizer hrandomizer internalBudget

/-- Local counter laws use one uniform base and the joint law of the two interpreted starts.
They assert no independence between counter attempts. -/
theorem SamplingLaws.counter [SampleableType Response] [SampleableType H]
    (modulus bottomBudget internalBudget : ℕ) (hbottom : bottomBudget ≤ modulus)
    (hinternal : internalBudget ≤ modulus) [SampleableType (Fin modulus)]
    (hash : HashInstance PP T X H S)
    (interpretation : Interpretation PP H (Fin modulus) Response)
    (hseed : interpretation.publicParameter <$> ($ᵗ Response) =ᵈ hash.thf.seedGen)
    (hpair : interpretation.chainPair <$> ($ᵗ Response) =ᵈ
      (do let left ← ($ᵗ H); let right ← ($ᵗ H); pure (left, right)))
    (hbase : interpretation.retryRandomizer <$> ($ᵗ Response) =ᵈ ($ᵗ (Fin modulus))) :
    SamplingLaws hash .pairedCounter
      (RetrySampling.counter modulus bottomBudget internalBudget hbottom hinternal) interpretation
      (RetryInterpretation.counter modulus bottomBudget internalBudget hbottom hinternal
        interpretation) where
  publicParameter := hseed
  starts := hpair
  bottomCoins := by
    simpa [sampleResponseFamily, RetryInterpretation.counter, RetrySampling.counter,
      Functor.map_map, Function.comp_def] using hbase
  internalCoins := by
    simpa [sampleResponseFamily, RetryInterpretation.counter, RetrySampling.counter,
      Functor.map_map, Function.comp_def] using hbase

/-- Local projected bind laws compose while retaining the one actual ideal cache. -/
theorem ideal_bind_projected {D A B : Type} [DecidableEq D] [SampleableType Response]
    (first : OracleComp (PRFScheme.PRFOracleSpec D Response) A)
    (next : A → OracleComp (PRFScheme.PRFOracleSpec D Response) B)
    (firstSample : ProbComp A) (nextSample : A → ProbComp B)
    (cache : (D →ₒ Response).QueryCache)
    (hfirst : (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response)) first).run' cache =ᵈ
      firstSample)
    (hnext : ∀ result ∈ support
        ((simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response)) first).run cache),
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
        (next result.1)).run' result.2 =ᵈ nextSample result.1) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
      (first >>= next)).run' cache =ᵈ (firstSample >>= nextSample) := by
  rw [simulateQ_bind, StateT.run'_bind']
  calc
    _ =ᵈ (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response)) first).run cache >>=
        fun result => nextSample result.1 :=
      OracleComp.EvalDistEq.bind_congr_of_support _ hnext
    _ = (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response)) first).run' cache >>=
        nextSample := by simp [StateT.run'_eq, bind_map_left]
    _ =ᵈ _ := hfirst.bind_left nextSample

/-- Independent finite programs in disjoint fresh query regions have their local product law.
The proof frames future regions through each real cached execution. -/
theorem ideal_mOfFn_fresh_regions {D A : Type} [DecidableEq D] [SampleableType Response]
    (n : ℕ) (programs : Fin n → OracleComp (PRFScheme.PRFOracleSpec D Response) A)
    (samples : Fin n → ProbComp A) (regions : Fin n → Set D)
    (hseparate : ∀ i j d, i ≠ j → d ∈ regions i → d ∈ regions j → False)
    (hqueries : ∀ i, AllQueriesSatisfy (programs i)
      (fun query => ∀ d, query = Sum.inr d → d ∈ regions i))
    (hlaw : ∀ i cache, (∀ d ∈ regions i, cache d = none) →
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
        (programs i)).run' cache =ᵈ samples i)
    (cache : (D →ₒ Response).QueryCache) (hfresh : ∀ i d, d ∈ regions i → cache d = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
      (Fin.mOfFn n programs)).run' cache =ᵈ Fin.mOfFn n samples := by
  induction n generalizing cache with
  | zero => exact EvalDistEq.refl _
  | succ n ih =>
    let tailPrograms := fun i : Fin n => programs i.succ
    let tailSamples := fun i : Fin n => samples i.succ
    let tailRegions := fun i : Fin n => regions i.succ
    have htailSep : ∀ i j d, i ≠ j → d ∈ tailRegions i → d ∈ tailRegions j → False := by
      intro i j d hij
      exact hseparate i.succ j.succ d (fun h => hij (Fin.succ_injective n h))
    have hstep := ideal_bind_projected (programs 0)
      (fun first => (fun rest : Fin n → A => (Fin.cons first rest : Fin (n + 1) → A)) <$>
        Fin.mOfFn n tailPrograms)
      (samples 0)
      (fun first => (fun rest : Fin n → A => (Fin.cons first rest : Fin (n + 1) → A)) <$>
        Fin.mOfFn n tailSamples) cache (hlaw 0 cache (hfresh 0)) (by
        intro result hresult
        have hfreshTail : ∀ i d, d ∈ tailRegions i → result.2 d = none := by
          intro i d hd
          have havoid : AllQueriesSatisfy (programs 0)
              (fun query => ∀ d', query = Sum.inr d' → d' ≠ d) :=
            (hqueries 0).mono (fun query hquery d' hinput hsame =>
              hseparate 0 i.succ d (fun heq => Fin.succ_ne_zero i heq.symm)
                (hsame ▸ hquery d' hinput) hd)
          rw [ideal_cache_frame d (programs 0) havoid cache result hresult]
          exact hfresh i.succ d hd
        rw [simulateQ_map, state_run'_map]
        exact (ih tailPrograms tailSamples tailRegions htailSep
          (fun i => hqueries i.succ) (fun i => hlaw i.succ) result.2 hfreshTail).map _)
    simpa only [Fin.mOfFn, map_eq_bind_pure_comp, Function.comp_def] using hstep

/-- Complete grouped pairs and their individual cells are equivalent finite data. -/
@[expose] def pairTableEquiv (H : Type) (groups : ℕ) :
    (Fin groups → H × H) ≃ ((Fin groups × Fin 2) → H) where
  toFun pairs cell := if cell.2.val = 0 then (pairs cell.1).1 else (pairs cell.1).2
  invFun table group := (table (group, 0), table (group, 1))
  left_inv pairs := by funext group; rfl
  right_inv table := by
    funext cell
    rcases cell with ⟨group, half⟩
    refine Fin.cases ?_ (fun tail => ?_) half
    · rfl
    · have htail : tail = 0 := Subsingleton.elim _ _
      subst tail
      rfl

/-- The coordinate decoder retains exactly the reached half of each complete pair. -/
@[expose] def readPairs (S : Shape) (pairs : Fin ((S.v + 1) / 2) → H × H) : Fin S.v → H :=
  fun i => if (startHalf i).val = 0 then (pairs (startGroup S i)).1
    else (pairs (startGroup S i)).2

/-- Grouped independent pair draws supply the full IID start-vector law, including odd chain
counts. The unused final half is projected away only after proving the joint pair law. -/
theorem paired_start_projection [SampleableType H] (S : Shape) :
    readPairs S <$> Fin.mOfFn ((S.v + 1) / 2)
      (fun _ => (do let left ← ($ᵗ H); let right ← ($ᵗ H); pure (left, right))) =ᵈ
      Fin.mOfFn S.v (fun _ => ($ᵗ H)) := by
  let : MeasurableSpace H := ⊤
  have hpair : (do let left ← ($ᵗ H); let right ← ($ᵗ H); pure (left, right)) =
      ($ᵗ (H × H)) := (SampleableType.uniformSample_prod_eq_bind H H).symm
  have hpairs : Fin.mOfFn ((S.v + 1) / 2) (fun _ => ($ᵗ (H × H))) =ᵈ
      ($ᵗ (Fin ((S.v + 1) / 2) → H × H)) := by
    apply EvalDistEq.of_evalDist_eq
    rw [evalDist_mOfFn, RetryPlan.evalDist_iid_coins]
  have hvec : Fin.mOfFn S.v (fun _ => ($ᵗ H)) =ᵈ ($ᵗ (Fin S.v → H)) := by
    apply EvalDistEq.of_evalDist_eq
    rw [evalDist_mOfFn, RetryPlan.evalDist_iid_coins]
  let cell := fun i : Fin S.v => (startGroup S i, startHalf i)
  have hrestrict : (fun table : (Fin ((S.v + 1) / 2) × Fin 2) → H => table ∘ cell) <$>
      ($ᵗ ((Fin ((S.v + 1) / 2) × Fin 2) → H)) =ᵈ ($ᵗ (Fin S.v → H)) := by
    apply EvalDistEq.of_evalDist_eq
    exact evalDist_map_table_comp_injective ($ᵗ (Fin S.v → H))
      ($ᵗ ((Fin ((S.v + 1) / 2) × Fin 2) → H))
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
      (startGroup_half_injective S)
  have htable := (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (pairTableEquiv H ((S.v + 1) / 2)).bijective).map
      (fun table : (Fin ((S.v + 1) / 2) × Fin 2) → H => table ∘ cell)
  rw [hpair]
  refine (hpairs.map (readPairs S)).trans ?_
  have hdecode : readPairs S <$> ($ᵗ (Fin ((S.v + 1) / 2) → H × H)) =ᵈ
      (fun table : (Fin ((S.v + 1) / 2) × Fin 2) → H => table ∘ cell) <$>
        ($ᵗ ((Fin ((S.v + 1) / 2) × Fin 2) → H)) := by
    rw [Functor.map_map] at htable
    exact htable
  exact hdecode.trans (hrestrict.trans hvec.symm)

/-- The fresh-region product law reindexes to any finite coordinate type. -/
theorem ideal_mPi_fresh_regions {D A I : Type} [DecidableEq D] [Fintype I]
    [SampleableType Response]
    (programs : I → OracleComp (PRFScheme.PRFOracleSpec D Response) A)
    (samples : I → ProbComp A) (regions : I → Set D)
    (hseparate : ∀ i j d, i ≠ j → d ∈ regions i → d ∈ regions j → False)
    (hqueries : ∀ i, AllQueriesSatisfy (programs i)
      (fun query => ∀ d, query = Sum.inr d → d ∈ regions i))
    (hlaw : ∀ i cache, (∀ d ∈ regions i, cache d = none) →
      (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
        (programs i)).run' cache =ᵈ samples i)
    (cache : (D →ₒ Response).QueryCache) (hfresh : ∀ i d, d ∈ regions i → cache d = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
      (Fintype.mPi programs)).run' cache =ᵈ Fintype.mPi samples := by
  unfold Fintype.mPi
  rw [simulateQ_map, state_run'_map]
  apply EvalDistEq.map
  let e := (Fintype.equivFin I).symm
  exact ideal_mOfFn_fresh_regions _ (fun i => programs (e i)) (fun i => samples (e i))
    (fun i => regions (e i))
    (fun i j d hij => hseparate (e i) (e j) d (fun h => hij (e.injective h)))
    (fun i => hqueries (e i)) (fun i => hlaw (e i)) cache (fun i => hfresh (e i))

/-- Query every start once per actual response group, retaining both halves together. -/
noncomputable def startQueries (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response) (pp : PP) :
    OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response)
      (OTSPosition S → Fin S.v → H) := by
  let : Fintype (OTSPosition S) := Fintype.ofFinite _
  exact Fintype.mPi fun p => match layout with
    | .iid => Fin.mOfFn S.v fun i =>
        interpretation.chainStart <$> PRFScheme.functionQuery (.start pp p i)
    | .pairedCounter => do
        let pairs ← Fin.mOfFn ((S.v + 1) / 2) fun group =>
          interpretation.chainPair <$> PRFScheme.functionQuery (.start pp p group)
        pure (fun i => if (startHalf i).val = 0 then (pairs (startGroup S i)).1
          else (pairs (startGroup S i)).2)

/-- One start-coordinate program uses precisely its layout's grouped response family. -/
@[expose] def coordinateStarts (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response) (pp : PP) (p : OTSPosition S) :
    OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response)
      (Fin S.v → H) :=
  match layout with
  | .iid => Fin.mOfFn S.v fun i =>
      interpretation.chainStart <$> PRFScheme.functionQuery (.start pp p i)
  | .pairedCounter => readPairs S <$> Fin.mOfFn ((S.v + 1) / 2) fun group =>
      interpretation.chainPair <$> PRFScheme.functionQuery (.start pp p group)

/-- Fresh complete start responses project to independent individual chain starts. -/
theorem coordinateStarts_ideal_fresh [SampleableType H] [SampleableType Response]
    (hash : HashInstance PP T X H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)] (pp : PP) (p : OTSPosition S)
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : ∀ i : StartIndex S layout, cache (.start pp p i) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response)) (coordinateStarts layout sampling interpretation pp p)).run' cache =ᵈ
        Fin.mOfFn S.v (fun _ => ($ᵗ H)) := by
  cases layout with
  | iid =>
      simp only [coordinateStarts, ← Fin.mOfFn_map, simulateQ_map, state_run'_map]
      rw [ideal_fin_queries_fresh S.v (fun i => .start pp p i)
        (fun i j h => by cases h; rfl) cache hfresh, Fin.mOfFn_map]
      exact mOfFn_evalDistEq _ _ _ (fun _ => laws.starts)
  | pairedCounter =>
      simp only [coordinateStarts, ← Fin.mOfFn_map, simulateQ_map, state_run'_map]
      rw [ideal_fin_queries_fresh ((S.v + 1) / 2) (fun i => .start pp p i)
        (fun i j h => by cases h; rfl) cache hfresh, Fin.mOfFn_map]
      exact ((mOfFn_evalDistEq _ _ _ (fun _ => laws.starts)).map (readPairs S)).trans
        (paired_start_projection S)

private theorem queries_map {ι A B : Type} {spec : OracleSpec ι}
    (f : A → B) (program : OracleComp spec A) (pred : ι → Prop)
    (h : AllQueriesSatisfy program pred) : AllQueriesSatisfy (f <$> program) pred := by
  rw [allQueriesSatisfy_def] at h ⊢
  exact (isQueryBound_map_iff _ _ _ _ _).mpr h

private theorem queries_mPi {ι A I : Type} {spec : OracleSpec ι} [Fintype I]
    (program : I → OracleComp spec A) (pred : ι → Prop)
    (h : ∀ i, AllQueriesSatisfy (program i) pred) :
    AllQueriesSatisfy (Fintype.mPi program) pred := by
  unfold Fintype.mPi
  apply queries_map
  exact allQueriesSatisfy_fin_mOfFn _ _ (fun _ => h _)

/-- Start programs access only the start region of their full OTS coordinate. -/
theorem coordinateStarts_queries (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response) (pp : PP) (p : OTSPosition S) :
    AllQueriesSatisfy (coordinateStarts (M := M) layout sampling interpretation pp p)
      (fun query => ∀ d, query = Sum.inr d → ∃ i : StartIndex S layout, d = .start pp p i) := by
  cases layout <;> simp only [coordinateStarts]
  · apply allQueriesSatisfy_fin_mOfFn
    intro i
    apply queries_map
    unfold PRFScheme.functionQuery
    rw [allQueriesSatisfy_query_iff]
    intro d hd
    cases hd
    exact ⟨i, rfl⟩
  · apply queries_map
    apply allQueriesSatisfy_fin_mOfFn
    intro i
    apply queries_map
    unfold PRFScheme.functionQuery
    rw [allQueriesSatisfy_query_iff]
    intro d hd
    cases hd
    exact ⟨i, rfl⟩

/-- All OTS start vectors retain their joint independent law through one ideal cache. -/
theorem startQueries_ideal_fresh [SampleableType H] [SampleableType Response]
    (hash : HashInstance PP T X H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)] (pp : PP)
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : ∀ p i, cache (.start pp p i) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response)) (startQueries layout sampling interpretation pp)).run' cache =ᵈ
        Hypertree.sampleStarts S := by
  let : Fintype (OTSPosition S) := Fintype.ofFinite _
  have heq : startQueries layout sampling interpretation pp =
      Fintype.mPi (coordinateStarts (M := M) (S := S) layout sampling interpretation pp) := by
    unfold startQueries coordinateStarts
    dsimp only
    apply congrArg (Fintype.mPi (m := OracleComp _))
    funext p
    cases layout <;> simp only [map_eq_bind_pure_comp, Function.comp_def]
    rfl
  rw [heq, Hypertree.sampleStarts]
  apply ideal_mPi_fresh_regions (regions := fun p => {d | ∃ i, d = .start pp p i})
  · intro p q d hpq hp hq
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨j, h⟩ := hq
    cases h
    exact hpq rfl
  · exact coordinateStarts_queries layout sampling interpretation pp
  · intro p table hf
    exact coordinateStarts_ideal_fresh hash layout sampling interpretation retry laws pp p table
      (fun i => hf _ ⟨i, rfl⟩)
  · intro p d hd
    obtain ⟨i, rfl⟩ := hd
    exact hfresh p i

/-- Bottom retry coins come from the exact bounded attempt or single-base request family. -/
@[expose] def bottomCoinsQuery (layout : Layout) (sampling : RetrySampling R)
    (retry : RetryInterpretation layout sampling Response) (pp : PP) (ep : Epoch S) (msg : M) :
    OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response)
      sampling.bottom.Coins :=
  retry.bottomCoins <$> responseFamilyQueries layout sampling.bottom.budget
    (fun i => .retry pp (bottomPosition S ep) (bottomMessage ep msg)
      (bottomRetryIndex layout sampling ep i))

/-- A fixed internal tape is derived using its child-root message and actual request family. -/
@[expose] def internalCoinsQuery (layout : Layout) (sampling : RetrySampling R)
    (retry : RetryInterpretation layout sampling Response) (pp : PP)
    (p : UpperPosition S) (root : H) :
    OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response)
      sampling.internal.Coins :=
  retry.internalCoins <$> responseFamilyQueries layout sampling.internal.budget
    (fun i => .retry pp p.val (internalMessage p root)
      (internalRetryIndex layout sampling p i))

/-- Every response-family request remains in the supplied finite input region. -/
theorem responseFamilyQueries_queries {D : Type} (layout : Layout) (budget : ℕ)
    (input : RetryIndex layout budget → D) :
    AllQueriesSatisfy (responseFamilyQueries (Response := Response) layout budget input)
      (fun query => ∀ d, query = Sum.inr d → ∃ i, d = input i) := by
  cases layout <;> simp only [responseFamilyQueries]
  · apply allQueriesSatisfy_fin_mOfFn
    intro i
    unfold PRFScheme.functionQuery
    rw [allQueriesSatisfy_query_iff]
    intro d hd
    cases hd
    exact ⟨i, rfl⟩
  · apply queries_map
    unfold PRFScheme.functionQuery
    rw [allQueriesSatisfy_query_iff]
    intro d hd
    cases hd
    exact ⟨(), rfl⟩

/-- A fresh bottom family decodes to the captured bottom coin sampler. -/
theorem bottomCoinsQuery_ideal_fresh [SampleableType H] [SampleableType Response]
    (hash : HashInstance PP T X H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)] (pp : PP) (ep : Epoch S) (msg : M)
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : ∀ i, cache (.retry pp (bottomPosition S ep) (bottomMessage ep msg)
      (bottomRetryIndex layout sampling ep i)) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response)) (bottomCoinsQuery layout sampling retry pp ep msg)).run' cache =ᵈ
        sampling.sampleBottom := by
  unfold bottomCoinsQuery
  rw [simulateQ_map, state_run'_map, responseFamilyQueries_ideal_fresh layout _ _
    (hinj := by
      cases layout
      · intro i j h
        simpa [bottomRetryIndex] using h
      · exact fun _ _ _ => Subsingleton.elim _ _) _ hfresh]
  exact laws.bottomCoins

/-- A fresh fixed internal family decodes to the captured internal coin sampler. -/
theorem internalCoinsQuery_ideal_fresh [SampleableType H] [SampleableType Response]
    (hash : HashInstance PP T X H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)] (pp : PP) (p : UpperPosition S) (root : H)
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : ∀ i, cache (.retry pp p.val (internalMessage p root)
      (internalRetryIndex layout sampling p i)) = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response)) (internalCoinsQuery layout sampling retry pp p root)).run' cache =ᵈ
        sampling.sampleInternal := by
  unfold internalCoinsQuery
  rw [simulateQ_map, state_run'_map, responseFamilyQueries_ideal_fresh layout _ _
    (hinj := by
      cases layout
      · intro i j h
        simpa [internalRetryIndex] using h
      · exact fun _ _ _ => Subsingleton.elim _ _) _ hfresh]
  exact laws.internalCoins

/-- The complete eager internal table has its joint captured product law. -/
theorem internalCoinsQueries_ideal_fresh [SampleableType H] [SampleableType Response]
    (hash : HashInstance PP T X H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)] (pp : PP) (roots : UpperPosition S → H)
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : ∀ p i, cache (.retry pp p.val (internalMessage p (roots p))
      (internalRetryIndex layout sampling p i)) = none) :
    letI : Fintype (UpperPosition S) := Fintype.ofFinite _
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response)) (Fintype.mPi fun p =>
        internalCoinsQuery layout sampling retry pp p (roots p))).run' cache =ᵈ
          Hypertree.sampleUpperCoins S sampling.sampleInternal := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  rw [Hypertree.sampleUpperCoins]
  apply ideal_mPi_fresh_regions (regions := fun p =>
    {d | ∃ i, d = .retry pp p.val (internalMessage p (roots p))
      (internalRetryIndex layout sampling p i)})
  · intro p q d hpq hp hq
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨j, h⟩ := hq
    have hp : p.val = q.val := by
      exact Option.some.inj (congrArg (fun d : Domain PP M H R S layout sampling =>
        match d with | .retry _ pos _ _ => some pos | _ => none) h)
    exact hpq (Subtype.ext hp)
  · intro p
    unfold internalCoinsQuery
    apply queries_map
    exact responseFamilyQueries_queries _ _ _
  · intro p table hf
    exact internalCoinsQuery_ideal_fresh hash layout sampling interpretation retry laws
      pp p (roots p) table (fun i => hf _ ⟨i, rfl⟩)
  · intro p d hd
    obtain ⟨i, rfl⟩ := hd
    exact hfresh p i

/-- Eager shared-oracle key material fixes all internal tapes before adaptive signing. -/
noncomputable def keyMaterialQueries (hash : HashInstance PP T X H S) (layout : Layout)
    (sampling : RetrySampling R) (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) :
    OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response)
      (GXMSS.PublicKey PP H × Hypertree.SecretKey PP H sampling.internal.Coins S) := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  exact do
    let pp ← interpretation.publicParameter <$> PRFScheme.functionQuery .publicSeed
    let starts ← startQueries layout sampling interpretation pp
    let ends := Hypertree.endpoints hash pp starts
    let coins ← Fintype.mPi fun p : UpperPosition S =>
      internalCoinsQuery layout sampling retry pp p (componentRoot hash pp ends (childTree S p))
    pure (Hypertree.keys hash pp starts coins)

private theorem functionQuery_queries {D : Type} (input : D) (pred : D → Prop)
    (h : pred input) : AllQueriesSatisfy (PRFScheme.functionQuery (R := Response) input)
      (fun query => ∀ d, query = Sum.inr d → pred d) := by
  unfold PRFScheme.functionQuery
  rw [allQueriesSatisfy_query_iff]
  intro d hd
  cases hd
  exact h

private theorem functionQuery_ideal_fresh {D : Type} [DecidableEq D]
    [SampleableType Response] (input : D) (cache : (D →ₒ Response).QueryCache)
    (hfresh : cache input = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := D) (R := Response))
      (PRFScheme.functionQuery input)).run' cache = ($ᵗ Response) := by
  rw [PRFScheme.simulateQ_prfIdealQueryImpl_functionQuery]
  unfold OracleSpec.randomOracle
  rw [StateT.run'_eq, QueryImpl.withCaching_run_none _ hfresh]
  simp [map_eq_bind_pure_comp, bind_assoc]

/-- A predicate holding at every start request holds throughout the start-table program. -/
theorem startQueries_queries (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response) (pp : PP)
    (pred : Domain PP M H R S layout sampling → Prop)
    (h : ∀ p i, pred (.start pp p i)) :
    AllQueriesSatisfy (startQueries layout sampling interpretation pp)
      (fun query => ∀ d, query = Sum.inr d → pred d) := by
  let : Fintype (OTSPosition S) := Fintype.ofFinite _
  unfold startQueries
  apply queries_mPi
  intro p
  cases layout
  · apply allQueriesSatisfy_fin_mOfFn
    intro i
    apply queries_map
    exact functionQuery_queries _ _ (h p i)
  · apply allQueriesSatisfy_bind
    · apply allQueriesSatisfy_fin_mOfFn
      intro i
      apply queries_map
      exact functionQuery_queries _ _ (h p i)
    · intro pairs
      exact allQueriesSatisfy_pure _ _

/-- A predicate holding at every fixed retry request holds throughout eager internal sampling. -/
theorem internalCoinsQueries_queries (layout : Layout) (sampling : RetrySampling R)
    (retry : RetryInterpretation layout sampling Response) (pp : PP)
    (roots : UpperPosition S → H) (pred : Domain PP M H R S layout sampling → Prop)
    (h : ∀ p i, pred (.retry pp p.val (internalMessage p (roots p))
      (internalRetryIndex layout sampling p i))) :
    letI : Fintype (UpperPosition S) := Fintype.ofFinite _
    AllQueriesSatisfy (Fintype.mPi fun p => internalCoinsQuery layout sampling retry pp p (roots p))
      (fun query => ∀ d, query = Sum.inr d → pred d) := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  apply queries_mPi
  intro p
  unfold internalCoinsQuery
  apply queries_map
  exact (responseFamilyQueries_queries (Response := Response) layout _ _).mono
    (fun query hq d hd => by obtain ⟨i, rfl⟩ := hq d hd; exact h p i)

/-- The ideal cached key generator has the actual direct joint key distribution. -/
theorem keyMaterialQueries_ideal [SampleableType H] [SampleableType Response]
    (hash : HashInstance PP T X H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)] :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response)) (keyMaterialQueries hash layout sampling interpretation retry)).run' ∅ =ᵈ
        Hypertree.keygen hash sampling := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  unfold keyMaterialQueries Hypertree.keygen
  dsimp only
  apply ideal_bind_projected
  · rw [simulateQ_map, state_run'_map, functionQuery_ideal_fresh _ _ (QueryCache.empty_apply _)]
    exact laws.publicParameter
  · intro seed hseed
    have hseedFresh : ∀ d, d ≠ (.publicSeed : Domain PP M H R S layout sampling) →
        seed.2 d = none := by
      intro d hd
      rw [ideal_cache_frame d _ (queries_map _ _ _
        (functionQuery_queries _ _ (Ne.symm hd))) ∅ seed hseed]
      exact QueryCache.empty_apply _
    apply ideal_bind_projected
    · exact startQueries_ideal_fresh hash layout sampling interpretation retry laws seed.1 seed.2
        (fun p i => hseedFresh _ (by intro h; cases h))
    · intro starts hstarts
      have hinternal : ∀ p i, starts.2 (.retry seed.1 p.val
          (internalMessage p (componentRoot hash seed.1
            (Hypertree.endpoints hash seed.1 starts.1) (childTree S p)))
          (internalRetryIndex layout sampling p i)) = none := by
        intro p i
        rw [ideal_cache_frame _ _ (startQueries_queries _ _ _ _ _
          (fun _ _ => by intro h; cases h)) seed.2 starts hstarts]
        exact hseedFresh _ (by intro h; cases h)
      apply ideal_bind_projected
      · exact internalCoinsQueries_ideal_fresh hash layout sampling interpretation retry laws
          seed.1 _ starts.2 hinternal
      · intro result _
        exact EvalDistEq.refl _


/-- The oracle signer reuses its full eager signing core and queries only fresh bottom coins. -/
noncomputable def oracleScheme (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) [DecidableEq H] :
    SyncSignatureAlg
      (OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response))
      M (GXMSS.PublicKey PP H) (Hypertree.SecretKey PP H sampling.internal.Coins S)
      (Hypertree.Signature R H S) (Epoch S) where
  keygen := keyMaterialQueries hash layout sampling interpretation retry
  sign sk ep msg := do
    let coins ← bottomCoinsQuery layout sampling retry sk.seed ep msg
    pure (signWithCoins hash family sampling sk ep msg coins)
  verify := Hypertree.verify hash family

/-- Unconsumed global epochs have no cached bottom retry responses. -/
@[expose] def RetryFresh (layout : Layout) (sampling : RetrySampling R) (pp : PP)
    (history : SyncSignatureUnforgeability.History (Epoch S) M (Hypertree.Signature R H S))
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache) : Prop :=
  ∀ ep, history ep = none → ∀ msg i,
    cache (.retry pp (bottomPosition S ep) (bottomMessage ep msg)
      (bottomRetryIndex layout sampling ep i)) = none

private theorem retry_position_eq (layout : Layout) (sampling : RetrySampling R)
    {pp qq : PP} {p q : OTSPosition S} {m : Message S M H p} {n : Message S M H q}
    {i : RetryIndex layout (retryBudget sampling p)}
    {j : RetryIndex layout (retryBudget sampling q)}
    (h : (Query.retry pp p m i : Domain PP M H R S layout sampling) = .retry qq q n j) : p = q :=
  Option.some.inj (congrArg (fun d : Domain PP M H R S layout sampling =>
    match d with | .retry _ pos _ _ => some pos | _ => none) h)

/-- Setup never queries any bottom retry input, even for an arbitrary future message. -/
theorem keyMaterialQueries_avoids_bottom (hash : HashInstance PP T X H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (pp : PP) (ep : Epoch S) (msg : M) (i : RetryIndex layout sampling.bottom.budget) :
    AllQueriesSatisfy (keyMaterialQueries hash layout sampling interpretation retry)
      (fun query => ∀ d, query = Sum.inr d → d ≠ .retry pp (bottomPosition S ep)
        (bottomMessage ep msg) (bottomRetryIndex layout sampling ep i)) := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  unfold keyMaterialQueries
  apply allQueriesSatisfy_bind
  · apply queries_map
    apply functionQuery_queries
    intro h
    cases h
  · intro seed
    apply allQueriesSatisfy_bind
    · apply startQueries_queries
      intro p j h
      cases h
    · intro starts
      apply allQueriesSatisfy_bind
      · apply internalCoinsQueries_queries
        intro p j h
        have hp := retry_position_eq layout sampling h
        have hl := congrArg (fun pos : OTSPosition S => pos.1.1.val) hp
        exact p.property (by simpa only [bottomPosition, positionAt_layer] using hl)
      · intro coins
        exact allQueriesSatisfy_pure _ _

/-- Actual reachable setup caches are fresh for every unconsumed bottom request. -/
theorem keyMaterialQueries_retryFresh [SampleableType Response]
    (hash : HashInstance PP T X H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (result : (GXMSS.PublicKey PP H × Hypertree.SecretKey PP H sampling.internal.Coins S) ×
      (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := Domain PP M H R S layout sampling) (R := Response))
      (keyMaterialQueries hash layout sampling interpretation retry)).run ∅)) :
    RetryFresh layout sampling result.1.2.seed SyncSignatureUnforgeability.emptyHistory
      result.2 := by
  intro ep _ msg i
  rw [ideal_cache_frame _ _ (keyMaterialQueries_avoids_bottom hash layout sampling interpretation
    retry result.1.2.seed ep msg i) ∅ result hresult]
  exact QueryCache.empty_apply _

/-- Fresh ideal signing projects to the captured direct signer, preserving optional failures. -/
theorem oracleSign_ideal_fresh [SampleableType H] [SampleableType Response] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (sk : Hypertree.SecretKey PP H sampling.internal.Coins S) (ep : Epoch S) (msg : M)
    (history : SyncSignatureUnforgeability.History (Epoch S) M (Hypertree.Signature R H S))
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : RetryFresh layout sampling sk.seed history cache) (hunused : history ep = none) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response)) ((oracleScheme hash family layout sampling interpretation retry).sign
        sk ep msg)).run' cache =ᵈ (Hypertree.scheme hash family sampling).sign sk ep msg := by
  change (simulateQ (PRFScheme.prfIdealQueryImpl
    (D := Domain PP M H R S layout sampling) (R := Response))
    (bottomCoinsQuery layout sampling retry sk.seed ep msg >>=
    fun coins => pure (signWithCoins hash family sampling sk ep msg coins))).run' cache =ᵈ
      (signWithCoins hash family sampling sk ep msg) <$> sampling.sampleBottom
  rw [map_eq_bind_pure_comp]
  apply ideal_bind_projected
  · exact bottomCoinsQuery_ideal_fresh hash layout sampling interpretation retry laws
      sk.seed ep msg cache (hfresh ep hunused msg)
  · intro result _
    exact EvalDistEq.refl _

/-- One consumed epoch changes no cached retry response belonging to any other epoch. -/
theorem oracleSign_preserves_fresh [SampleableType Response] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (sk : Hypertree.SecretKey PP H sampling.internal.Coins S) (ep : Epoch S) (msg : M)
    (history : SyncSignatureUnforgeability.History (Epoch S) M (Hypertree.Signature R H S))
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : RetryFresh layout sampling sk.seed history cache)
    (result : Option (Hypertree.Signature R H S) ×
      (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hresult : result ∈ support ((simulateQ (PRFScheme.prfIdealQueryImpl
      (D := Domain PP M H R S layout sampling) (R := Response))
      ((oracleScheme hash family layout sampling interpretation retry).sign
        sk ep msg)).run cache)) :
    RetryFresh layout sampling sk.seed (Function.update history ep (some (msg, result.1)))
      result.2 := by
  intro other hunused message i
  have hne : other ≠ ep := by intro h; subst other; simp [Function.update] at hunused
  have havoid : AllQueriesSatisfy
      ((oracleScheme hash family layout sampling interpretation retry).sign sk ep msg)
      (fun query => ∀ d, query = Sum.inr d → d ≠ .retry sk.seed (bottomPosition S other)
        (bottomMessage other message) (bottomRetryIndex layout sampling other i)) := by
    apply allQueriesSatisfy_bind
    · unfold bottomCoinsQuery
      apply queries_map
      exact (responseFamilyQueries_queries (Response := Response) layout _ _).mono
        (fun query hq d hd hsame => by
          obtain ⟨j, rfl⟩ := hq d hd
          exact hne ((positionAt_bottom_injective S)
            (retry_position_eq layout sampling hsame)).symm)
    · intro coins
      exact allQueriesSatisfy_pure _ _
  rw [ideal_cache_frame _ _ havoid cache result hresult]
  exact hfresh other (by simpa [Function.update, hne] using hunused) message i

/-- One persistent ideal cache gives the direct adaptive signing law at fixed key material. -/
private theorem ideal_fixed_run_projected {A : Type}
    [SampleableType H] [SampleableType Response] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (sk : Hypertree.SecretKey PP H sampling.internal.Coins S)
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Epoch S) M (Hypertree.Signature R H S)) A)
    (history : SyncSignatureUnforgeability.History (Epoch S) M (Hypertree.Signature R H S))
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : RetryFresh layout sampling sk.seed history cache) :
    Prod.map id Prod.fst <$> (simulateQ (GXMSS.PRFDerived.SigningSimulation.idealHandler
      (oracleScheme hash family layout sampling interpretation retry) sk) program).run
        (history, cache) =ᵈ (simulateQ (GXMSS.PRFDerived.SigningSimulation.fixedHandler
          (Hypertree.scheme hash family sampling) sk) program).run history := by
  apply signingRun_projected
    (oracleScheme hash family layout sampling interpretation retry)
    (Hypertree.scheme hash family sampling) sk sk (RetryFresh layout sampling sk.seed)
    ?_ ?_ program history cache hfresh
  · intro ep msg hist table hf hu
    exact oracleSign_ideal_fresh hash family layout sampling interpretation retry laws
      sk ep msg hist table hf hu
  · intro ep msg hist table hf _ result hr
    exact oracleSign_preserves_fresh hash family layout sampling interpretation retry
      sk ep msg hist table hf result hr

/-- Interpreting the nested signing handler uses the same persistent ideal cache. -/
private theorem ideal_fixed_interaction_correspondence {A : Type}
    [SampleableType H] [SampleableType Response] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (sk : Hypertree.SecretKey PP H sampling.internal.Coins S)
    (program : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Epoch S) M (Hypertree.Signature R H S)) A)
    (history : SyncSignatureUnforgeability.History (Epoch S) M (Hypertree.Signature R H S))
    (cache : (Domain PP M H R S layout sampling →ₒ Response).QueryCache)
    (hfresh : RetryFresh layout sampling sk.seed history cache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response)) ((simulateQ (signingHandler
        (oracleScheme hash family layout sampling interpretation retry) sk) program).run
          history)).run' cache =ᵈ
      (simulateQ
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
          (StateT (SyncSignatureUnforgeability.History (Epoch S) M
            (Hypertree.Signature R H S)) ProbComp) +
          SyncSignatureUnforgeability.signingOracle (Hypertree.scheme hash family sampling) sk)
        program).run history := by
  have hfixed := ideal_fixed_run_projected hash family layout sampling interpretation retry laws
    sk program history cache hfresh
  have hcompose := simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling) (R := Response))
    (signingHandler (oracleScheme hash family layout sampling interpretation retry) sk)
    program history cache
  rw [StateT.run'_eq, hcompose]
  simp only [Functor.map_map]
  exact hfixed

/-- Source adversaries retain their original ambient sampling and synchronized signing interface. -/
abbrev SchemeAdversary (PP H M R : Type) (S : Shape) :=
  SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch S) M
    (Hypertree.Signature R H S)

/-- One function-oracle program performs setup and the entire adaptive interaction. -/
noncomputable def oracleInteraction [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) (adv : SchemeAdversary PP H M R S) :
    OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response)
      (SyncSignatureUnforgeability.ExperimentResult (GXMSS.PublicKey PP H) (Epoch S) M
        (Hypertree.Signature R H S)) := do
  let pair ← keyMaterialQueries hash layout sampling interpretation retry
  let result ← (simulateQ (signingHandler
    (oracleScheme hash family layout sampling interpretation retry) pair.2)
      (adv.forge pair.1)).run SyncSignatureUnforgeability.emptyHistory
  pure (pair.1, result.1, result.2)

/-- Local seed, grouped-start and retry-coin laws transport the complete ideal interaction.
The observation retains the public key, forgery and full first-request history, including
failures. -/
theorem oracleInteraction_ideal_eq_interaction
    [SampleableType H] [SampleableType Response] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (laws : SamplingLaws hash layout sampling interpretation retry)
    [DecidableEq (Domain PP M H R S layout sampling)]
    (adv : SchemeAdversary PP H M R S) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := Domain PP M H R S layout sampling)
      (R := Response))
      (oracleInteraction hash family layout sampling interpretation retry adv)).run'
        ∅ =ᵈ SyncSignatureUnforgeability.interaction
          (Hypertree.scheme hash family sampling) adv := by
  unfold oracleInteraction SyncSignatureUnforgeability.interaction
  dsimp only [Hypertree.scheme]
  apply ideal_bind_projected
  · exact keyMaterialQueries_ideal hash layout sampling interpretation retry laws
  · intro material hmaterial
    apply ideal_bind_projected
    · exact ideal_fixed_interaction_correspondence hash family layout sampling interpretation retry
        laws material.1.2 (adv.forge material.1.1) SyncSignatureUnforgeability.emptyHistory
          material.2 (keyMaterialQueries_retryFresh hash layout sampling interpretation retry
            material hmaterial)
    · intro result _
      exact EvalDistEq.refl _


end GXMSS.Hypertree.PRFDerived.Unforgeability
