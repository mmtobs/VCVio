/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.RetryPlan

/-!
# Strategy-indexed accepted-hash retry

The hash challenger tests its acceptance predicate on the captured randomizer sequence. Its
result retains the selected randomizer, first successful attempt and entire consumed prefix.
The transport to encoding retries compares complete results before forgetting metadata.
-/

public section

namespace GXMSS.Hypertree.Security.HashRetry

open Encoding Encoding.IncomparableEncoding

/-- Complete first-success metadata for a hash-acceptance search. -/
inductive Result (R : Type) where
  | success (randomizer : R) (attempt : ℕ) (consumed : List R)
  | exhausted (consumed : List R)

namespace Result

variable {R : Type} {n radix : ℕ}

/-- The native hash challenge exposes the selected randomizer or exhaustion. -/
@[expose] def output : Result R → Option R
  | .success r _ _ => some r
  | .exhausted _ => none

/-- Recover the full encoding result through public hash evaluation and decoding. -/
@[expose] def toEncoding (word : R → Codeword n radix) : Result R → IndexedResult R n radix
  | .success r attempt consumed => .success (word r) r attempt consumed
  | .exhausted consumed => .exhausted consumed

/-- Forgetting metadata commutes with decoding the selected randomizer. -/
theorem output_toEncoding (word : R → Codeword n radix) (result : Result R) :
    (result.toEncoding word).output = result.output.map (fun r => (word r, r)) := by
  cases result <;> rfl

end Result

variable {R PP M E : Type} {n radix : ℕ}

/-- Search a fixed finite randomizer sequence, stopping at its first accepted hash. -/
@[expose] def search (accepts : R → Bool) : (k : ℕ) → (Fin k → R) → Result R
  | 0, _ => .exhausted []
  | k + 1, randomizers =>
      if accepts (randomizers 0) then .success (randomizers 0) 1 [randomizers 0]
      else match search accepts k (fun i => randomizers i.succ) with
        | .success r attempt consumed => .success r (attempt + 1) (randomizers 0 :: consumed)
        | .exhausted consumed => .exhausted (randomizers 0 :: consumed)

/-- The selected native randomizer satisfies the actual hash acceptance test. -/
theorem accepts_of_search_output (accepts : R → Bool) (k : ℕ) (randomizers : Fin k → R)
    {r : R} (h : (search accepts k randomizers).output = some r) : accepts r = true := by
  induction k with
  | zero => simp [search, Result.output] at h
  | succ k ih =>
    simp only [search] at h
    split_ifs at h with ha
    · have heq : randomizers 0 = r := by simpa [Result.output] using h
      simpa [← heq] using ha
    · cases hs : search accepts k (fun i => randomizers i.succ) with
      | exhausted consumed => simp [hs, Result.output] at h
      | success r' attempt consumed =>
        have heq : r' = r := by simpa [hs, Result.output] using h
        subst r'
        exact ih (fun i => randomizers i.succ) (by simp [hs, Result.output])

/-- Equal acceptance and full-word observations identify the complete retry result, including
exhaustion, the first successful attempt and exact ordered consumed prefix. -/
theorem retryIndexed_eq_search
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (accepts : R → Bool) (word : R → Codeword n radix)
    (hvalue : ∀ r, enc.value pp msg r ep = if accepts r then some (word r) else none)
    (k : ℕ) (randomizers : Fin k → R) :
    enc.retryIndexed (m := Id) pp msg ep k randomizers =
      (search accepts k randomizers).toEncoding word := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [retryIndexed_id_succ, hvalue]
    simp only [search]
    split_ifs with ha
    · rfl
    · rw [ih (fun i => randomizers i.succ)]
      cases search accepts k (fun i => randomizers i.succ) <;> rfl

/-- Any finite retry plan, including a modular counter plan, has the same full fixed-coin result
under the hash observation. No independence of the randomizers is assumed. -/
theorem run_eq_search (plan : RetryPlan R)
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP) (msg : M) (ep : E)
    (accepts : R → Bool) (word : R → Codeword n radix)
    (hvalue : ∀ r, enc.value pp msg r ep = if accepts r then some (word r) else none)
    (coins : plan.Coins) :
    plan.run enc pp msg ep coins =
      (search accepts plan.budget (plan.randomizers coins)).toEncoding word :=
  retryIndexed_eq_search enc pp msg ep accepts word hvalue plan.budget (plan.randomizers coins)

end GXMSS.Hypertree.Security.HashRetry
