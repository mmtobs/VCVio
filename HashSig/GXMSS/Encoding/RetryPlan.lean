/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.RetryIndexed
public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Finite explicit retry plans

A finite coin value determines the complete ordered randomizer sequence. First-success search
uses the indexed retry operation and preserves its success, exhaustion, attempt and consumed-prefix
data. Independent attempt coins and a single modular-counter base are distinct sampling layouts.
-/

public section

namespace GXMSS.Encoding

/-- A finite explicit coin space and its bounded deterministic randomizer sequence. -/
structure RetryPlan (R : Type) where
  /-- Coins fixed before the deterministic first-success search. -/
  Coins : Type
  /-- The complete coin space is finite; no enumeration is required by the search. -/
  [finiteCoins : Finite Coins]
  /-- Maximum number of encoding attempts, including the empty budget. -/
  budget : ℕ
  /-- Ordered randomizers, including correlated sequences derived from one coin. -/
  randomizers : Coins → Fin budget → R

namespace RetryPlan

open IncomparableEncoding MeasureTheory ProbabilityTheory OracleComp

variable {PP M R E : Type} {n radix : ℕ}

/-- Run a bounded first-success search using fixed explicit coins. -/
@[expose] def run (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (coins : plan.Coins) : IndexedResult R n radix :=
  enc.retryIndexed (m := Id) pp msg ep plan.budget (plan.randomizers coins)

/-- A zero budget returns exhaustion with no consumed randomizers. -/
theorem run_of_budget_eq_zero (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (coins : plan.Coins) (h : plan.budget = 0) :
    plan.run enc pp msg ep coins = .exhausted [] := by
  cases plan with
  | mk Coins budget randomizers =>
    change budget = 0 at h
    subst budget
    rfl

/-- Exact first-success semantics for a deterministic randomizer sequence. Success identifies
its zero-based first successful index, one-based attempt and ordered consumed prefix; exhaustion
consumes the complete sequence. -/
@[expose] def IsFirstSuccess
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    {k : ℕ} (randomizers : Fin k → R) : IndexedResult R n radix → Prop
  | .success word selected attempt consumed =>
      ∃ i : Fin k, selected = randomizers i ∧ attempt = i.val + 1 ∧
        consumed = (List.ofFn randomizers).take (i.val + 1) ∧
        enc.value pp msg (randomizers i) ep = some word ∧
        ∀ j : Fin k, j.val < i.val → enc.value pp msg (randomizers j) ep = none
  | .exhausted consumed =>
      consumed = List.ofFn randomizers ∧
        ∀ i : Fin k, enc.value pp msg (randomizers i) ep = none

/-- Indexed deterministic retry returns exactly the first success or full exhaustion. -/
theorem retryIndexed_isFirstSuccess
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (k : ℕ) (randomizers : Fin k → R) :
    IsFirstSuccess enc pp msg ep randomizers
      (enc.retryIndexed (m := Id) pp msg ep k randomizers) := by
  induction k with
  | zero =>
    change [] = List.ofFn randomizers ∧ _
    exact ⟨rfl, fun i => Fin.elim0 i⟩
  | succ k ih =>
    rw [IncomparableEncoding.retryIndexed_id_succ]
    cases hfirst : enc.value pp msg (randomizers 0) ep with
    | some word =>
      simp only [IsFirstSuccess]
      refine ⟨0, rfl, rfl, ?_, hfirst, ?_⟩
      · simp [List.ofFn_succ]
      · intro j hj
        simp at hj
    | none =>
      have hrest := ih (fun i => randomizers i.succ)
      cases hresult : enc.retryIndexed (m := Id) pp msg ep k
          (fun i => randomizers i.succ) with
      | exhausted consumed =>
        simp only [hresult, IsFirstSuccess] at hrest ⊢
        refine ⟨?_, ?_⟩
        · simpa [List.ofFn_succ] using congrArg (List.cons (randomizers 0)) hrest.1
        · intro i
          exact Fin.cases hfirst (fun j => hrest.2 j) i
      | success word selected attempt consumed =>
        simp only [hresult, IsFirstSuccess] at hrest ⊢
        obtain ⟨i, hi, hattempt, hconsumed, hword, hbefore⟩ := hrest
        refine ⟨i.succ, hi, ?_, ?_, hword, ?_⟩
        · simp [hattempt]
        · simp [List.ofFn_succ, hconsumed]
        · intro j hj
          refine Fin.cases (fun _ => hfirst) (fun j' hj' => ?_) j hj
          exact hbefore j' (by simpa using hj')

/-- Fixed-coin retry preserves its first successful index and exact consumed-prefix metadata. -/
theorem run_isFirstSuccess (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (coins : plan.Coins) :
    IsFirstSuccess enc pp msg ep (plan.randomizers coins) (plan.run enc pp msg ep coins) :=
  retryIndexed_isFirstSuccess enc pp msg ep plan.budget (plan.randomizers coins)

/-- A successful returned word and randomizer re-encode to that same word. -/
theorem value_eq_some_of_run_output_eq_some (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (coins : plan.Coins) {word : Codeword n radix} {r : R}
    (h : (plan.run enc pp msg ep coins).output = some (word, r)) :
    enc.value pp msg r ep = some word := by
  have hspec := plan.run_isFirstSuccess enc pp msg ep coins
  cases hresult : plan.run enc pp msg ep coins with
  | exhausted consumed => simp [hresult, IndexedResult.output] at h
  | success word' selected attempt consumed =>
    have heq : word' = word ∧ selected = r := by
      simpa [hresult, IndexedResult.output] using h
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hresult, IsFirstSuccess] at hspec
    obtain ⟨i, hi, _, _, hword, _⟩ := hspec
    simpa [← hi] using hword

/-- Returned exhaustion is equivalent to failure at every bounded attempt. -/
theorem run_output_eq_none_iff (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (coins : plan.Coins) :
    (plan.run enc pp msg ep coins).output = none ↔
      ∀ i : Fin plan.budget, enc.value pp msg (plan.randomizers coins i) ep = none := by
  have hspec := plan.run_isFirstSuccess enc pp msg ep coins
  cases hresult : plan.run enc pp msg ep coins with
  | exhausted consumed =>
    simp only [hresult, IsFirstSuccess] at hspec
    simp [IndexedResult.output, hspec.2]
  | success word selected attempt consumed =>
    simp only [hresult, IsFirstSuccess] at hspec
    obtain ⟨i, _, _, _, hword, _⟩ := hspec
    simp only [IndexedResult.output, reduceCtorEq, false_iff]
    intro hall
    rw [hall i] at hword
    contradiction

/-- Exhaustion consumes the complete ordered randomizer sequence. -/
theorem consumed_of_run_eq_exhausted (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (coins : plan.Coins) {consumed : List R}
    (h : plan.run enc pp msg ep coins = .exhausted consumed) :
    consumed = List.ofFn (plan.randomizers coins) := by
  have hspec := plan.run_isFirstSuccess enc pp msg ep coins
  rw [h] at hspec
  exact hspec.1

/-- Successful metadata gives an in-budget attempt equal to the consumed-prefix length. -/
theorem attempt_of_run_eq_success (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (coins : plan.Coins) {word : Codeword n radix} {r : R} {attempt : ℕ}
    {consumed : List R}
    (h : plan.run enc pp msg ep coins = .success word r attempt consumed) :
    0 < attempt ∧ attempt ≤ plan.budget ∧ consumed.length = attempt ∧
      consumed = (List.ofFn (plan.randomizers coins)).take attempt := by
  have hspec := plan.run_isFirstSuccess enc pp msg ep coins
  rw [h] at hspec
  obtain ⟨i, _, rfl, rfl, _, _⟩ := hspec
  have hi : i.val + 1 ≤ plan.budget := i.isLt
  simp [List.length_take, hi]

/-- Equality of the encoding observations at every bounded read preserves the complete retry
result, including its failure and trace metadata. -/
theorem retryIndexed_eq_of_values_eq {PP' M' E' : Type}
    (enc : IncomparableEncoding PP M R E n radix)
    (enc' : IncomparableEncoding PP' M' R E' n radix)
    (pp : PP) (pp' : PP') (msg : M) (msg' : M') (ep : E) (ep' : E')
    (k : ℕ) (randomizers : Fin k → R)
    (h : ∀ i, enc.value pp msg (randomizers i) ep =
      enc'.value pp' msg' (randomizers i) ep') :
    enc.retryIndexed (m := Id) pp msg ep k randomizers =
      enc'.retryIndexed (m := Id) pp' msg' ep' k randomizers := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [IncomparableEncoding.retryIndexed_id_succ,
      IncomparableEncoding.retryIndexed_id_succ, h 0]
    cases enc'.value pp' msg' (randomizers 0) ep' with
    | some word => rfl
    | none => rw [ih (fun i => randomizers i.succ) (fun i => h i.succ)]

/-- Fixed coins support exact retry-result transport from equal encoding reads. -/
theorem run_eq_of_values_eq {PP' M' E' : Type} (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix)
    (enc' : IncomparableEncoding PP' M' R E' n radix)
    (pp : PP) (pp' : PP') (msg : M) (msg' : M') (ep : E) (ep' : E')
    (coins : plan.Coins)
    (h : ∀ i, enc.value pp msg (plan.randomizers coins i) ep =
      enc'.value pp' msg' (plan.randomizers coins i) ep') :
    plan.run enc pp msg ep coins = plan.run enc' pp' msg' ep' coins :=
  retryIndexed_eq_of_values_eq enc enc' pp pp' msg msg' ep ep'
    plan.budget (plan.randomizers coins) h

/-- A sampled successful output has a coin witness and a valid re-encoding. -/
theorem value_eq_some_of_mem_sampled_output (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (sample : ProbComp plan.Coins) {word : Codeword n radix} {r : R}
    (h : some (word, r) ∈ support
      ((fun coins => (plan.run enc pp msg ep coins).output) <$> sample)) :
    enc.value pp msg r ep = some word := by
  obtain ⟨coins, _, hcoins⟩ := OracleComp.mem_support_map_peel _ sample h
  exact plan.value_eq_some_of_run_output_eq_some enc pp msg ep coins hcoins.symm

/-- Sampling a finite tape and then searching it has the same complete returned-result law as
sampling each reached index. `ProbComp` draws are lossless, so the unused tape suffix introduces
no mass loss. The claim includes exhaustion and trace metadata. -/
theorem retryIndexed_sample_tape
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (sample : ProbComp R) (k : ℕ) :
    (fun coins => enc.retryIndexed (m := Id) pp msg ep k coins) <$>
        Fin.mOfFn k (fun _ => sample) =ᵈ
      enc.retryIndexed pp msg ep k (fun _ => sample) := by
  induction k with
  | zero => exact EvalDistEq.refl _
  | succ k ih =>
    simp only [Fin.mOfFn, map_bind, map_pure]
    rw [IncomparableEncoding.retryIndexed]
    apply EvalDistEq.bind_right sample
    intro r
    simp only [IncomparableEncoding.retryIndexed_id_succ, Fin.cons_zero, Fin.cons_succ]
    cases hfirst : enc.value pp msg r ep with
    | some word =>
      exact OracleComp.EvalDistEq.bind_const
        (Fin.mOfFn k (fun _ => sample))
        (pure (.success word r 1 [r]) : ProbComp (IndexedResult R n radix))
    | none =>
      let prepend : IndexedResult R n radix → IndexedResult R n radix
        | .success word selected attempt consumed =>
            .success word selected (attempt + 1) (r :: consumed)
        | .exhausted consumed => .exhausted (r :: consumed)
      have hleft :
          (Fin.mOfFn k (fun _ => sample) >>= fun rest =>
            pure (prepend (enc.retryIndexed (m := Id) pp msg ep k rest))) =
          prepend <$> ((fun coins => enc.retryIndexed (m := Id) pp msg ep k coins) <$>
            Fin.mOfFn k (fun _ => sample)) := by
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        rfl
      change (Fin.mOfFn k (fun _ => sample) >>= fun rest =>
        pure (prepend (enc.retryIndexed (m := Id) pp msg ep k rest))) =ᵈ _
      rw [hleft]
      refine (ih.map prepend).trans ?_
      apply EvalDistEq.of_forall_prEvent_eq
      intro p
      congr 1
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
      congr 1
      funext result
      cases result <;> rfl

/-- Each attempt's coin is its randomizer; no dependence between distinct coordinates is imposed
by this deterministic definition. Sampling the tuple independently supplies the IID law. -/
@[expose, reducible] def iid (R : Type) [Finite R] (k : ℕ) : RetryPlan R where
  Coins := Fin k → R
  budget := k
  randomizers coins := coins

/-- A single modular base followed by bounded consecutive offsets. The budget bound prevents
repeated randomizers in one complete sequence, including when the traversal crosses zero. -/
@[expose, reducible] def counter (modulus k : ℕ) (hk : k ≤ modulus) : RetryPlan (Fin modulus) where
  Coins := Fin modulus
  budget := k
  randomizers base i := base + Fin.castLE hk i

/-- Counter traversal starts at its base when the budget is nonempty. -/
@[simp] theorem counter_randomizers_zero (modulus k : ℕ) (hk : k + 1 ≤ modulus)
    (base : Fin modulus) :
    (counter modulus (k + 1) hk).randomizers base 0 = base := by
  let : NeZero modulus := ⟨by omega⟩
  change base + Fin.castLE hk 0 = base
  have hcast : Fin.castLE hk (0 : Fin (k + 1)) = (0 : Fin modulus) := Fin.ext rfl
  rw [hcast, add_zero]

/-- Distinct bounded offsets give distinct randomizers even across modular wraparound. -/
theorem counter_randomizers_injective (modulus k : ℕ) (hk : k ≤ modulus)
    (base : Fin modulus) : Function.Injective ((counter modulus k hk).randomizers base) := by
  intro i j hij
  have hcast : Fin.castLE hk i = Fin.castLE hk j := add_left_cancel hij
  apply Fin.ext
  exact congrArg (fun x : Fin modulus => x.val) hcast

/-- The complete randomizer tuple has the product law when the attempt coins are drawn
independently. This local statement includes every attempted coordinate jointly. -/
theorem evalDist_iid_randomizers [SampleableType R] [MeasurableSpace R]
    (k : ℕ) :
    𝒟[(iid R k).randomizers <$> Fin.mOfFn k (fun _ => ($ᵗ R : ProbComp R))] =
      Measure.pi (fun _ : Fin k => 𝒟[($ᵗ R : ProbComp R)]) := by
  simpa [iid] using evalDist_mOfFn k (fun _ => ($ᵗ R : ProbComp R))

/-- A uniformly sampled IID coin tuple has the product measure of its attempt randomizers. -/
theorem evalDist_iid_coins [SampleableType R] [MeasurableSpace R]
    [MeasurableSingletonClass R] (k : ℕ) :
    𝒟[($ᵗ (iid R k).Coins)] =
      Measure.pi (fun _ : Fin k => 𝒟[($ᵗ R : ProbComp R)]) := by
  rw [SampleableType.evalDist_uniformSample]
  have h := evalDist_mOfFn_const_uniform k ($ᵗ R : ProbComp R)
    SampleableType.evalDist_uniformSample
  rw [evalDist_mOfFn] at h
  exact h.symm

/-- IID fixed-coin search exhausts with the power of its one-attempt failure mass.
This law is specific to the product coin distribution. -/
theorem iid_exhaustion_mass [SampleableType R] [MeasurableSpace R]
    [MeasurableSingletonClass R]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (k : ℕ) :
    𝒟[($ᵗ (iid R k).Coins)]
        {coins | ((iid R k).run enc pp msg ep coins).output = none} =
      (𝒟[($ᵗ R : ProbComp R)] {r | enc.value pp msg r ep = none}) ^ k := by
  rw [evalDist_iid_coins]
  have hevent : {coins : Fin k → R | ((iid R k).run enc pp msg ep coins).output = none} =
      Set.univ.pi (fun _ : Fin k => {r | enc.value pp msg r ep = none}) := by
    ext coins
    simp [run_output_eq_none_iff]
  rw [hevent, Measure.pi_pi]
  simp

/-- Canonical uniform IID coins and reached-index sampling have the same complete retry law. -/
theorem iid_run_evalDistEq_retryIndexed [SampleableType R]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (k : ℕ) :
    (fun coins => (iid R k).run enc pp msg ep coins) <$> ($ᵗ (iid R k).Coins) =ᵈ
      enc.retryIndexed pp msg ep k (fun _ => ($ᵗ R : ProbComp R)) := by
  let : MeasurableSpace R := ⊤
  have htape : ($ᵗ (iid R k).Coins) =ᵈ Fin.mOfFn k (fun _ => ($ᵗ R : ProbComp R)) := by
    apply EvalDistEq.of_evalDist_eq
    rw [evalDist_iid_coins, evalDist_mOfFn]
  exact (htape.map (fun coins => (iid R k).run enc pp msg ep coins)).trans
    (retryIndexed_sample_tape enc pp msg ep ($ᵗ R) k)

/-- Forgetting only trace metadata recovers the established IID retry computation, including
returned exhaustion. -/
theorem iid_run_output_evalDistEq_retry [SampleableType R]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (k : ℕ) :
    (fun coins => ((iid R k).run enc pp msg ep coins).output) <$>
        ($ᵗ (iid R k).Coins) =ᵈ enc.retry ($ᵗ R) pp msg ep k := by
  have h := (iid_run_evalDistEq_retryIndexed enc pp msg ep k).map IndexedResult.output
  rw [← enc.retry_eq_indexed_constant ($ᵗ R) pp msg ep k] at h
  simpa only [Functor.map_map, Function.comp_def] using h

/-- The complete modular-counter tuple is the pushforward of one uniform base.
This joint law preserves its dependence between attempts. -/
theorem evalDist_counter_randomizers (modulus k : ℕ) (hk : k ≤ modulus)
    [SampleableType (Fin modulus)] [MeasurableSpace (Fin modulus)]
    [MeasurableSingletonClass (Fin modulus)] :
    𝒟[(counter modulus k hk).randomizers <$> ($ᵗ (Fin modulus))] =
      (uniformOn Set.univ : Measure (Fin modulus)).map
        ((counter modulus k hk).randomizers) := by
  rw [evalDist_map _ Measurable.of_discrete,
    SampleableType.evalDist_uniformSample]

/-- Every individual counter attempt is uniformly distributed, although the tuple is correlated. -/
theorem counter_randomizer_uniform (modulus k : ℕ) (hk : k ≤ modulus)
    [SampleableType (Fin modulus)] (i : Fin k) :
    (fun base => (counter modulus k hk).randomizers base i) <$>
      ($ᵗ (Fin modulus)) =ᵈ ($ᵗ (Fin modulus)) := by
  let : NeZero modulus := ⟨Nat.ne_zero_of_lt (Fin.size_positive' : 0 < modulus)⟩
  apply SampleableType.map_uniformSample_evalDistEq_of_bijective
  exact (Equiv.addRight (Fin.castLE hk i)).bijective

end RetryPlan

end GXMSS.Encoding
