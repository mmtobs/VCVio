/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Absorbing filters for adaptive simulations

Projecting a state to an absorbing rejection state preserves each good returned output.
The equality concerns successful-output measures and permits computations to lose mass.
-/

public section

namespace GXMSS.Reductions.FilteredSimulation
open OracleComp OracleSpec ENNReal

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
