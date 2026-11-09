/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.SimSemantics.StateT.Measure
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Absorbing filters for adaptive simulations

Projecting a state to an absorbing rejection state preserves each good returned output.
The equality concerns successful-output measures and permits computations to lose mass.
-/

public section

namespace GXMSS.Reductions.FilteredSimulation
open OracleComp OracleSpec ENNReal

/-- Local joint distributional projections on reachable states preserve the complete adaptive
result and projected state, including returned failures and missing mass. -/
theorem map_simulateQ_run_evalDistEq_of_query
    {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}
    (left : QueryImpl spec (StateT σ₁ ProbComp))
    (right : QueryImpl spec (StateT σ₂ ProbComp))
    (project : σ₁ → σ₂) (inv : σ₁ → Prop)
    (hinv : QueryImpl.PreservesInv left inv)
    (hstep : ∀ t s, inv s →
      Prod.map id project <$> (left t).run s =ᵈ (right t).run (project s))
    (program : OracleComp spec α) (state : σ₁) (hstate : inv state) :
    Prod.map id project <$> (simulateQ left program).run state =ᵈ
      (simulateQ right program).run (project state) := by
  have hintertwines : QueryImpl.IntertwinesOn inv (fun s => pure (project s)) left right := by
    intro t s hs γ _ continuation
    have h := ((hstep t s hs).bind_left
      (fun result => continuation result.1 result.2)).evalDist_eq
    simpa only [pure_bind, bind_map_left, Prod.map_fst, Prod.map_snd, id_eq] using h
  let : MeasurableSpace (α × σ₂) := ⊤
  apply EvalDistEq.of_evalDist_eq
  have h := hintertwines.evalDist_simulateQ_run hinv program state hstate
    (fun result finalState => pure (result, finalState))
  simpa only [pure_bind, bind_pure_comp, map_pure, Prod.eta, bind_pure,
    Prod.map_def, id_eq] using h

/-- Absorbing optional-state simulations may return different answers after rejection. Their
complete optional result/state observations still agree when their surviving steps agree.
The discarded rejected suffix is lossless because both handlers take values in `ProbComp`. -/
theorem masked_simulateQ_run_evalDistEq
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (left right : QueryImpl spec (StateT (Option σ) ProbComp))
    (hleft : ∀ t, ∀ out ∈ support ((left t).run none), out.2 = none)
    (hright : ∀ t, ∀ out ∈ support ((right t).run none), out.2 = none)
    (hstep : ∀ t s, (left t).run (some s) =ᵈ (right t).run (some s))
    (program : OracleComp spec α) (state : Option σ) :
    (fun out => out.2.map (fun s => (out.1, s))) <$> (simulateQ left program).run state =ᵈ
      (fun out => out.2.map (fun s => (out.1, s))) <$>
        (simulateQ right program).run state := by
  have hnone (impl : QueryImpl spec (StateT (Option σ) ProbComp))
      (habsorb : ∀ t, ∀ out ∈ support ((impl t).run none), out.2 = none)
      (oa : OracleComp spec α) :
      (fun out => out.2.map (fun s => (out.1, s))) <$> (simulateQ impl oa).run none =ᵈ
        (pure (none : Option (α × σ)) : ProbComp _) := by
    have hpreserve : ∀ out ∈ support ((simulateQ impl oa).run none), out.2 = none :=
      simulateQ_run_preserves_inv_of_query impl (fun s => s = none)
        (fun t s hs out hout => by subst s; exact habsorb t out hout) oa none rfl
    rw [map_eq_bind_pure_comp]
    refine (OracleComp.EvalDistEq.bind_congr_of_support _ (fun out hout => ?_)).trans
      (OracleComp.EvalDistEq.bind_const _ (pure none))
    simp only [Function.comp_def, hpreserve out hout, Option.map_none]
    exact EvalDistEq.refl _
  induction program using OracleComp.inductionOn generalizing state with
  | pure result =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact EvalDistEq.refl _
  | query_bind t next ih =>
    cases state with
    | none => exact (hnone left hleft _).trans (hnone right hright _).symm
    | some s =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      exact (hstep t s).bind_congr (fun out => ih out.1 out.2)

/-- State projection through an absorbing filter preserves each good returned output, even when
bad paths later lose mass. This deliberately asserts no equality for bad or missing outputs. -/
theorem goodOutput_simulateQ_eq_filtered
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    [MeasurableSpace σ] [MeasurableSpace α]
    [MeasurableSingletonClass σ] [MeasurableSingletonClass α]
    (original : QueryImpl spec (StateT σ ProbComp))
    (filtered : QueryImpl spec (StateT (Option σ) ProbComp))
    (bad : σ → Bool)
    (transform : (t : spec.Domain) → spec.Range t × σ → spec.Range t)
    (htransform : ∀ t u s', bad s' = false → transform t (u, s') = u)
    (hmono : ∀ t s, bad s = true →
      ∀ z ∈ support ((original t).run s), bad z.2 = true)
    (habsorb : ∀ t, ∀ z ∈ support ((filtered t).run none), z.2 = none)
    (hstep : ∀ t s, bad s = false →
      (fun z => (transform t z, if bad z.2 then none else some z.2)) <$>
        (original t).run s = (filtered t).run (some s))
    (oa : OracleComp spec α) (s₀ : σ) (a : α) (s : σ)
    (hgood : bad s = false) :
    𝒟[(simulateQ original oa).run s₀] {(a, s)} =
      𝒟[(simulateQ filtered oa).run
        (if bad s₀ then none else some s₀)] {(a, some s)} := by
  classical
  simp only [← prEvent_eq_evalDist_singleton]
  have zeroOriginal (program : OracleComp spec α) (start : σ)
      (hbad : bad start = true) :
      𝒟[(simulateQ original program).run start] {(a, s)} = 0 := by
    rw [← prEvent_eq_evalDist_singleton]
    apply (OracleComp.prEvent_eq_zero_iff _ _).2
    intro z hz heq
    have hpres := OracleComp.simulateQ_run_preserves_inv_of_query
      original (fun x => bad x = true) hmono program start hbad z hz
    subst z
    exact Bool.false_ne_true (hgood.symm.trans hpres)
  have zeroFiltered (program : OracleComp spec α) :
      𝒟[(simulateQ filtered program).run none] {(a, some s)} = 0 := by
    rw [← prEvent_eq_evalDist_singleton]
    apply (OracleComp.prEvent_eq_zero_iff _ _).2
    intro z hz heq
    have hpres := OracleComp.simulateQ_run_preserves_inv_of_query
      filtered (fun x => x = none) (by
        intro t state hs z hz
        subst state
        exact habsorb t z hz) program none rfl z hz
    subst z
    cases hpres
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure x =>
    by_cases hbad : bad s₀ = true
    · have hsneq : s ≠ s₀ := by
        intro he
        subst s₀
        exact Bool.false_ne_true (hgood.symm.trans hbad)
      simpa [hbad, simulateQ_pure] using
        (fun (_ : x = a) (he : s₀ = s) => hsneq he.symm)
    · have hgood₀ : bad s₀ = false := by cases h : bad s₀ <;> simp_all
      simp [hgood₀, simulateQ_pure]
  | query_bind t cont ih =>
    by_cases hbad : bad s₀ = true
    · simpa only [hbad, ite_true, ← prEvent_eq_evalDist_singleton, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind] using
        (zeroOriginal ((liftM (OracleSpec.query t) :
          OracleComp spec (spec.Range t)) >>= cont) s₀ hbad).trans
          (zeroFiltered ((liftM (OracleSpec.query t) :
            OracleComp spec (spec.Range t)) >>= cont)).symm
    · have hgood₀ : bad s₀ = false := by cases h : bad s₀ <;> simp_all
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [hgood₀, Bool.false_eq_true, ite_false]
      rw [← hstep t s₀ hgood₀, bind_map_left]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      exact tsum_congr fun ⟨u, s'⟩ => by
        congr 1
        by_cases hbad' : bad s' = true
        · simp only [hbad', ite_true]
          simpa only [← prEvent_eq_evalDist_singleton] using
            (zeroOriginal (cont u) s' hbad').trans
              (zeroFiltered (cont (transform t (u, s')))).symm
        · have hgood' : bad s' = false := by cases h : bad s' <;> simp_all
          simpa [hgood', htransform t u s' hgood'] using ih u s'

/-- Summing preserved good singleton outputs preserves the entire good returned event. -/
theorem goodEvent_eq_filtered
    {α σ : Type}
    [MeasurableSpace (α × σ)] [MeasurableSpace (α × Option σ)]
    [MeasurableSingletonClass (α × σ)]
    [MeasurableSingletonClass (α × Option σ)]
    [DiscreteMeasurableSpace (α × σ)]
    [DiscreteMeasurableSpace (α × Option σ)]
    (original : ProbComp (α × σ))
    (filtered : ProbComp (α × Option σ)) (bad : σ → Bool)
    (event : α × σ → Bool)
    (hgood : ∀ z, event z = true → bad z.2 = false)
    (hpoint : ∀ z, bad z.2 = false →
      𝒟[original] {z} = 𝒟[filtered] {(z.1, some z.2)}) :
    𝒟[event <$> original] {true} =
      𝒟[(fun z => z.2.elim false (fun s => event (z.1, s))) <$> filtered] {true} := by
  classical
  let filteredEvent : α × Option σ → Bool :=
    fun z => z.2.elim false (fun s => event (z.1, s))
  change 𝒟[event <$> original] {true} = 𝒟[filteredEvent <$> filtered] {true}
  rw [evalDist_map_apply original Measurable.of_discrete (measurableSet_singleton true),
    evalDist_map_apply filtered Measurable.of_discrete (measurableSet_singleton true)]
  change 𝒟[original] {z | event z = true} =
    𝒟[filtered] {z | filteredEvent z = true}
  rw [← prEvent_eq_evalDist_of_discrete original (fun z => event z = true),
    ← prEvent_eq_evalDist_of_discrete filtered (fun z => filteredEvent z = true)]
  rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite]
  conv_rhs =>
    rw [ENNReal.tsum_prod']
  conv_lhs =>
    rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro a
  rw [tsum_option _ ENNReal.summable]
  simp only [filteredEvent, Option.elim_none,
    Option.elim_some, Bool.false_eq_true, ite_false, zero_add]
  exact tsum_congr fun s => by
    by_cases he : event (a, s) = true
    · simp only [he, ite_true]
      simpa only [prEvent_eq_evalDist_singleton, Prod.mk.eta] using
        hpoint (a, s) (hgood (a, s) he)
    · simp [he]


end GXMSS.Reductions.FilteredSimulation
