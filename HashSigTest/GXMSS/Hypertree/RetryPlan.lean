/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Family
public import HashSig.GXMSS.Encoding.RetryPlan
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Finite retry-plan and encoding-family controls

These controls distinguish first success, exhausted searches, zero attempts and modular
wraparound. Independent singleton codes also exhibit the absence of cross-coordinate assumptions.
-/

public section

namespace GXMSS.Encoding.HypertreeRetryProbe

open IncomparableEncoding

/-- The zero one-digit word. -/
@[expose] def wordZero : Codeword 1 2 := fun _ => 0

/-- The maximal one-digit word. -/
@[expose] def wordOne : Codeword 1 2 := fun _ => 1

/-- Boolean randomizers succeed exactly when true. -/
@[expose] def boolEncoding : IncomparableEncoding Unit Unit Bool Unit 1 2 where
  code := {wordZero}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r then some ⟨wordZero, by simp⟩ else none

/-- Empty plans return exhaustion without reading even a successful randomizer. -/
theorem zero_budget :
    (RetryPlan.iid Bool 0).run boolEncoding () () () (fun i => nomatch i) =
      .exhausted [] := rfl

/-- The IID layout retains the first success, its one-based index and exact consumed prefix. -/
theorem second_attempt :
    (RetryPlan.iid Bool 3).run boolEncoding () () () (fun i => i.val == 1) =
      .success wordZero true 2 [false, true] := rfl

/-- Early success does not include unused suffix coins in its consumption trace. -/
theorem early_success :
    (RetryPlan.iid Bool 3).run boolEncoding () () () (fun _ => true) =
      .success wordZero true 1 [true] := rfl

/-- Exhaustion retains every failed attempt in order. -/
theorem all_failed :
    (RetryPlan.iid Bool 3).run boolEncoding () () () (fun _ => false) =
      .exhausted [false, false, false] := rfl

/-- A modular traversal can wrap through zero before its first successful attempt. -/
@[expose] def counterEncoding : IncomparableEncoding Unit Unit (Fin 4) Unit 1 2 where
  code := {wordZero}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r = 0 then some ⟨wordZero, by simp⟩ else none

/-- The first two modular randomizers are three and zero, with success at the wrap point. -/
theorem counter_wrap_success :
    (RetryPlan.counter 4 3 (by decide)).run counterEncoding () () () 3 =
      .success wordZero 0 2 [3, 0] := rfl

/-- A counter with two positions never repeats its base at the second position. -/
theorem counter_two_no_repeat (base : Fin 2) :
    (RetryPlan.counter 2 2 (by decide)).randomizers base 0 ≠
      (RetryPlan.counter 2 2 (by decide)).randomizers base 1 := by
  intro h
  have hindices := RetryPlan.counter_randomizers_injective 2 2 (by decide) base h
  exact (by decide : (0 : Fin 2) ≠ 1) hindices

/-- Two singleton codes may contain comparable words at distinct complete coordinates. -/
@[expose] def separateCodes : Family Bool Unit (fun _ => Unit) Bool 1 2 where
  component b :=
    { code := {if b then wordOne else wordZero}
      incomparable := by
        intro x hx y hy hne
        exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
      encode _ _ _ _ := some ⟨if b then wordOne else wordZero, by simp⟩ }

/-- Cross-coordinate comparability is permitted by the family boundary. -/
theorem cross_coordinate_words_comparable : ¬ IncomparableWords wordZero wordOne := by
  simp [IncomparableWords, wordZero, wordOne]

/-- Incomparability within every coordinate does not supply the additional nondegeneracy law. -/
theorem separateCodes_not_noMaximumOutput : ¬ separateCodes.NoMaximumOutput := by
  intro h
  obtain ⟨i, hi⟩ := h true () () false wordOne rfl
  simp [wordOne] at hi

example := @RetryPlan.run_isFirstSuccess
example := @RetryPlan.run_eq_of_values_eq
example := @RetryPlan.iid_exhaustion_mass
example := @RetryPlan.iid_run_evalDistEq_retryIndexed
example := @RetryPlan.iid_run_output_evalDistEq_retry
example := @RetryPlan.evalDist_counter_randomizers
example := @RetryPlan.counter_randomizer_uniform

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``Family.noMaximumOutput_of_two_codewords,
    ``RetryPlan.run_isFirstSuccess,
    ``RetryPlan.value_eq_some_of_run_output_eq_some,
    ``RetryPlan.run_output_eq_none_iff,
    ``RetryPlan.attempt_of_run_eq_success,
    ``RetryPlan.run_eq_of_values_eq,
    ``RetryPlan.iid_exhaustion_mass,
    ``RetryPlan.retryIndexed_sample_tape,
    ``RetryPlan.iid_run_evalDistEq_retryIndexed,
    ``RetryPlan.iid_run_output_evalDistEq_retry,
    ``RetryPlan.evalDist_counter_randomizers,
    ``RetryPlan.counter_randomizer_uniform,
    ``counter_wrap_success,
    ``separateCodes_not_noMaximumOutput]

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Encoding.Family, `HashSig.GXMSS.Encoding.RetryPlan]
    #[(``Family.noMaximumOutput_of_two_codewords, `HashSig.GXMSS.Encoding.Family),
      (``RetryPlan.run_isFirstSuccess, `HashSig.GXMSS.Encoding.RetryPlan),
      (``RetryPlan.iid_run_output_evalDistEq_retry, `HashSig.GXMSS.Encoding.RetryPlan),
      (``RetryPlan.counter_randomizer_uniform, `HashSig.GXMSS.Encoding.RetryPlan)]
    #[]
    #[(``RetryPlan.run, `HashSig.GXMSS.Encoding.RetryPlan),
      (``Family.atEpoch, `HashSig.GXMSS.Encoding.Family)]

end GXMSS.Encoding.HypertreeRetryProbe
