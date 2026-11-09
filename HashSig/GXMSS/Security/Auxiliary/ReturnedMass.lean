/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Returned masses under uniform coordinate refresh

Refreshing one independent finite-table coordinate preserves every continuation measure.
If a continuation ignores the old coordinate, its first chain response can be supplied
from an independent draw without changing the returned event mass.
-/

public section

namespace GXMSS.Reductions.ReturnedMass
open ENNReal OracleComp OracleSpec

/-- Refreshing one coordinate of an explicitly calibrated nested uniform table preserves its law. -/
theorem uniform_nested_coordinate_resampling
    {I J H : Type} [Finite I] [Finite J] [DecidableEq I] [DecidableEq J]
    [SampleableType H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (draw : ProbComp (I → J → H))
    (hdraw : 𝒟[draw] = ProbabilityTheory.uniformOn Set.univ) (ep : I) (i : J) :
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← draw
      return Function.update starts ep (Function.update (starts ep) i x)] = 𝒟[draw] := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  let Flat := I × J → H
  let Nested := I → J → H
  let e : Flat ≃ Nested := Equiv.curry (I) (J) H
  have hvalue : 𝒟[($ᵗ H : ProbComp H)] = ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  have hflat : 𝒟[($ᵗ Flat : ProbComp Flat)] =
      ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  have hnested : 𝒟[draw] =
      ProbabilityTheory.uniformOn Set.univ := hdraw
  have hmap : 𝒟[e <$> ($ᵗ Flat : ProbComp Flat)] =
      𝒟[draw] := by
    rw [evalDist_map_of_discrete, hflat,
      ProbabilityTheory.uniformOn_univ_map_equiv e, hnested]
  have hupdate : ∀ (g : Flat) (x : H),
      e (Function.update g (ep, i) x) =
        Function.update (e g) ep (Function.update (e g ep) i x) := by
    intro g x
    funext ep' i'
    change Function.update g (ep, i) x (ep', i') =
      Function.update (e g) ep (Function.update (e g ep) i x) ep' i'
    by_cases hep : ep' = ep
    · subst ep'
      by_cases hi : i' = i
      · subst i'; simp [Function.update]
      · simp [Function.update, hi]
        rfl
    · simp [Function.update, hep]
      rfl
  have hflatUpdate := evalDist_bind_bind_update
    ($ᵗ H : ProbComp H) ($ᵗ Flat : ProbComp Flat)
    hvalue hflat (ep, i) (fun g => pure (e g))
  have hinner (x : H) :
      𝒟[draw >>= fun starts =>
        pure (Function.update starts ep (Function.update (starts ep) i x))] =
      𝒟[($ᵗ Flat : ProbComp Flat) >>= fun g =>
        pure (e (Function.update g (ep, i) x))] := by
    have hcross := evalDist_bind_bijective_uniform_cross
      ($ᵗ Flat : ProbComp Flat) (draw)
      hflat hnested e e.bijective
      (fun starts => pure
        (Function.update starts ep (Function.update (starts ep) i x)))
    simp_rw [← hupdate] at hcross
    exact hcross.symm
  calc
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← draw
      return Function.update starts ep (Function.update (starts ep) i x)]
        = 𝒟[do
          let x ← ($ᵗ H : ProbComp H)
          let g ← ($ᵗ Flat : ProbComp Flat)
          return e (Function.update g (ep, i) x)] := by
            rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
            simp_rw [hinner]
    _ = 𝒟[($ᵗ Flat : ProbComp Flat) >>= fun g => pure (e g)] := hflatUpdate
    _ = 𝒟[draw] := by
      rw [map_eq_bind_pure_comp] at hmap
      exact hmap

/-- Coordinate refresh remains valid under any continuation, including loss. -/
theorem uniform_nested_coordinate_resampling_bind
    {I J H α : Type} [Finite I] [Finite J] [DecidableEq I] [DecidableEq J]
    [SampleableType H] [MeasurableSpace H] [MeasurableSingletonClass H] [MeasurableSpace α]
    (draw : ProbComp (I → J → H))
    (hdraw : 𝒟[draw] = ProbabilityTheory.uniformOn Set.univ) (ep : I) (i : J)
    (f : (I → J → H) → ProbComp α) :
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← draw
      f (Function.update starts ep (Function.update (starts ep) i x))] =
      𝒟[draw >>= f] := by
  classical
  have hrefresh := uniform_nested_coordinate_resampling draw hdraw ep i
  have hprogram :
      (do
        let x ← ($ᵗ H : ProbComp H)
        let starts ← draw
        f (Function.update starts ep (Function.update (starts ep) i x))) =
      (do
        let x ← ($ᵗ H : ProbComp H)
        let starts ← draw
        pure (Function.update starts ep (Function.update (starts ep) i x))) >>= f := by
    simp only [bind_assoc, pure_bind]
  rw [hprogram, evalDist_bind_of_discrete, hrefresh, ← evalDist_bind_of_discrete]

/-- Pointwise equality of returned event masses integrates over a common discrete draw. -/
theorem evalDist_bind_event_eq_of_discrete
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace β]
    (mx : ProbComp α) (f g : α → ProbComp β)
    (event : Set β) (hevent : MeasurableSet event)
    (hfg : ∀ a, 𝒟[f a] event = 𝒟[g a] event) :
    𝒟[mx >>= f] event = 𝒟[mx >>= g] event := by
  apply le_antisymm
  · exact evalDist_bind_apply_mono_of_discrete mx f g hevent
      (fun a => (hfg a).le)
  · exact evalDist_bind_apply_mono_of_discrete mx g f hevent
      (fun a => (hfg a).ge)

/-- If the old selected coordinate is observationally unused, a first response can be generated
from an independent value. The assertion concerns the selected event without conditioning. -/
theorem independent_coordinate_image_mass
    {I J H A : Type} [Finite I] [Finite J] [DecidableEq I] [DecidableEq J]
    [SampleableType H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (draw : ProbComp (I → J → H))
    (hdraw : 𝒟[draw] = ProbabilityTheory.uniformOn Set.univ) (ep : I) (i : J)
    (image : H → A) (f : A → (I → J → H) → ProbComp Bool)
    (hignore : ∀ answer starts x,
      𝒟[f answer (Function.update starts ep (Function.update (starts ep) i x))] {true} =
        𝒟[f answer starts] {true}) :
    𝒟[draw >>= fun starts => f (image (starts ep i)) starts] {true} =
    𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← draw
      f (image x) starts] {true} := by
  classical
  have hresample := uniform_nested_coordinate_resampling_bind draw hdraw ep i
    (fun starts => f (image (starts ep i)) starts)
  calc
    _ = 𝒟[do
      let x ← ($ᵗ H : ProbComp H)
      let starts ← draw
      f (image ((Function.update starts ep (Function.update (starts ep) i x)) ep i))
        (Function.update starts ep (Function.update (starts ep) i x))] {true} :=
      congrArg (· {true}) hresample.symm
    _ = _ := by
      apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
      intro x
      apply evalDist_bind_event_eq_of_discrete _ _ _ {true} (measurableSet_singleton true)
      intro starts
      simpa only [Function.update_self] using hignore (image x) starts x

/-- A uniform selector accepting exactly one coordinate on a win pays its exact cardinality. -/
theorem uniform_selector_probability {S : Type} [Fintype S] [SampleableType S]
    (win : Bool) (selected : S → Bool)
    (hsingleton : win = true → ∃ target, ∀ s, selected s = true ↔ s = target)
    (himplies : ∀ s, selected s = true → win = true) :
    Pr{let s ← ($ᵗ S : ProbComp S)}[selected s = true] =
      if win = true then (Fintype.card S : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hwin : win = true
  · obtain ⟨target, htarget⟩ := hsingleton hwin
    simp only [hwin, ite_true]
    rw [prEvent_congr _ _ _ htarget]
    exact SampleableType.prEvent_uniformSample_eq_singleton target
  · simp only [hwin]
    apply (SampleableType.prEvent_uniformSample_eq_zero_iff
      (fun s : S => selected s = true)).2
    intro s hs
    exact hwin (himplies s hs)

/-- Pointwise selected returned mass integrates to its constant factor times the source event.
The source may diverge or otherwise lose mass. -/
theorem bind_true_mass_eq_mul_event {A : Type} [MeasurableSpace A]
    [DiscreteMeasurableSpace A] (source : ProbComp A) (branch : A → ProbComp Bool)
    (win : A → Bool) (factor : ℝ≥0∞)
    (hconditional : ∀ out ∈ support source,
      𝒟[branch out] {true} = if win out = true then factor else 0) :
    𝒟[source >>= branch] {true} = factor * 𝒟[source] {out | win out = true} := by
  have hae : ∀ᵐ out ∂𝒟[source],
      𝒟[branch out] {true} = if win out = true then factor else 0 :=
    evalDist.ae_of_forall_mem_support source _ MeasurableSet.of_discrete hconditional
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable, MeasureTheory.lintegral_congr_ae hae]
  have hfun : (fun out : A => if win out = true then factor else 0) =
      ({out | win out = true} : Set A).indicator (fun _ => factor) := by
    funext out
    by_cases h : win out = true <;> simp [h]
  rw [hfun, MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete]

end GXMSS.Reductions.ReturnedMass
