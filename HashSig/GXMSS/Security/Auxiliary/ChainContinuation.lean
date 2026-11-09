/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Chain

/-!
# Chain continuations

Chain splices over an arbitrary OTS coordinate type preserve endpoint-derived metadata
and materialized outputs whose selected-chain reads lie beyond the cut. Fixed coins are
explicit inputs to metadata preparation, so the equations retain retry exhaustion.
-/

public section

namespace GXMSS.Reductions.ChainContinuation

/-- A family of position-dependent chains, indexed by OTS coordinates and chain labels. -/
structure ChainFamily (I H : Type) (v : ℕ) where
  /-- Continue a chain from a given position for a given number of steps. -/
  chain : I → Fin v → ℕ → ℕ → H → H
  /-- Continuing for no steps preserves the supplied value. -/
  chain_zero : ∀ c i k x, chain c i k 0 x = x
  /-- Adjacent chain segments compose in their original order. -/
  chain_add : ∀ c i k s t x,
    chain c i k (s + t) x = chain c i (k + s) t (chain c i k s x)

variable {I H Coins Metadata Output : Type} {v : ℕ}

/-- Endpoints at a common final position. -/
@[expose] def endpoints (family : ChainFamily I H v) (n : ℕ)
    (starts : I → Fin v → H) : I → Fin v → H :=
  fun c i => family.chain c i 0 n (starts c i)

/-- Replace the response at positive position `cut + 1`, retaining earlier prefixes. -/
@[expose] def spliceValue [DecidableEq I] (family : ChainFamily I H v)
    (selected : I) (selectedChain : Fin v) (cut : ℕ) (answer : H)
    (starts : I → Fin v → H) (c : I) (i : Fin v) (position : ℕ) : H :=
  if _htarget : c = selected ∧ i = selectedChain then
    if position < cut + 1 then family.chain c i 0 position (starts c i)
    else family.chain c i (cut + 1) (position - (cut + 1)) answer
  else family.chain c i 0 position (starts c i)

/-- Endpoint table assembled from a spliced chain family. -/
@[expose] def spliceEndpoints [DecidableEq I] (family : ChainFamily I H v) (n : ℕ)
    (selected : I) (selectedChain : Fin v) (cut : ℕ) (answer : H)
    (starts : I → Fin v → H) : I → Fin v → H :=
  fun c i => spliceValue family selected selectedChain cut answer starts c i n

/-- Supplying the honest cut response recovers every unmodified chain prefix. -/
theorem spliceValue_honest [DecidableEq I] (family : ChainFamily I H v)
    (selected : I) (selectedChain : Fin v) (cut : ℕ) (starts : I → Fin v → H)
    (c : I) (i : Fin v) (position : ℕ) :
    spliceValue family selected selectedChain cut
      (family.chain selected selectedChain 0 (cut + 1) (starts selected selectedChain))
      starts c i position = family.chain c i 0 position (starts c i) := by
  unfold spliceValue
  split_ifs with htarget hbefore
  · rfl
  · rcases htarget with ⟨rfl, rfl⟩
    have hle : cut + 1 ≤ position := by omega
    simpa only [Nat.zero_add, Nat.add_sub_of_le hle] using
      (family.chain_add c i 0 (cut + 1)
        (position - (cut + 1)) (starts c i)).symm
  · rfl

/-- The honest splice recovers the complete endpoint table. -/
theorem spliceEndpoints_honest [DecidableEq I] (family : ChainFamily I H v) (n : ℕ)
    (selected : I) (selectedChain : Fin v) (cut : ℕ) (starts : I → Fin v → H) :
    spliceEndpoints family n selected selectedChain cut
      (family.chain selected selectedChain 0 (cut + 1) (starts selected selectedChain)) starts =
      endpoints family n starts := by
  funext c i
  exact spliceValue_honest family selected selectedChain cut starts c i n

/-- Advancing the splice by one step preserves every later prefix. -/
theorem spliceValue_advance [DecidableEq I] (family : ChainFamily I H v)
    (selected : I) (selectedChain : Fin v) (cut : ℕ) (answer : H)
    (starts : I → Fin v → H) (c : I) (i : Fin v) (position : ℕ)
    (hlate : c = selected → i = selectedChain → cut + 2 ≤ position) :
    spliceValue family selected selectedChain cut answer starts c i position =
      spliceValue family selected selectedChain (cut + 1)
        (family.chain selected selectedChain (cut + 1) 1 answer) starts c i position := by
  unfold spliceValue
  by_cases ht : c = selected ∧ i = selectedChain
  · obtain ⟨rfl, rfl⟩ := ht
    have hp := hlate rfl rfl
    have hcount : position - (cut + 1) = 1 + (position - (cut + 1 + 1)) := by omega
    simp only [and_self, ↓reduceDIte, show ¬position < cut + 1 by omega,
      show ¬position < cut + 1 + 1 by omega, ↓reduceIte]
    rw [hcount, family.chain_add]
  · simp only [ht, ↓reduceDIte]

/-- Advancing any nonfinal splice preserves the full endpoint table. -/
theorem spliceEndpoints_advance [DecidableEq I] (family : ChainFamily I H v) (n : ℕ)
    (selected : I) (selectedChain : Fin v) (cut : ℕ) (answer : H)
    (starts : I → Fin v → H) (hlate : cut + 2 ≤ n) :
    spliceEndpoints family n selected selectedChain cut answer starts =
      spliceEndpoints family n selected selectedChain (cut + 1)
        (family.chain selected selectedChain (cut + 1) 1 answer) starts := by
  funext c i
  exact spliceValue_advance family selected selectedChain cut answer starts c i n
    (fun _ _ => hlate)

/-- A splice at the final step installs the supplied response as the selected endpoint. -/
theorem spliceEndpoints_selected_final [DecidableEq I] (family : ChainFamily I H v)
    (selected : I) (selectedChain : Fin v) (cut : ℕ) (answer : H)
    (starts : I → Fin v → H) :
    spliceEndpoints family (cut + 1) selected selectedChain cut answer starts
      selected selectedChain = answer := by
  simp [spliceEndpoints, spliceValue, family.chain_zero]

/-- A zero splice ignores its old selected start at all positive selected positions. -/
theorem spliceValue_zero_start_update [DecidableEq I] (family : ChainFamily I H v)
    (selected : I) (selectedChain : Fin v) (answer : H)
    (starts : I → Fin v → H) (x : H) (c : I) (i : Fin v) (position : ℕ)
    (hpos : c = selected → i = selectedChain → 0 < position) :
    spliceValue family selected selectedChain 0 answer
      (Function.update starts selected (Function.update (starts selected) selectedChain x))
      c i position = spliceValue family selected selectedChain 0 answer starts c i position := by
  unfold spliceValue
  by_cases ht : c = selected ∧ i = selectedChain
  · have hp := hpos ht.1 ht.2
    simp [ht, show ¬position < 0 + 1 by omega]
  · have hstart :
        Function.update starts selected (Function.update (starts selected) selectedChain x)
          c i = starts c i := by
      by_cases hc : c = selected
      · subst c
        have hi : i ≠ selectedChain := fun hi => ht ⟨rfl, hi⟩
        simp [Function.update, hi]
      · simp [Function.update, hc]
    simp [ht, hstart]

/-- At a zero splice every positive endpoint is independent of the old selected start. -/
theorem spliceEndpoints_zero_start_update [DecidableEq I] (family : ChainFamily I H v)
    (n : ℕ) (selected : I) (selectedChain : Fin v) (answer : H)
    (starts : I → Fin v → H) (x : H) (hn : 0 < n) :
    spliceEndpoints family n selected selectedChain 0 answer
      (Function.update starts selected (Function.update (starts selected) selectedChain x)) =
      spliceEndpoints family n selected selectedChain 0 answer starts := by
  funext c i
  exact spliceValue_zero_start_update family selected selectedChain answer starts x c i n
    (fun _ _ => hn)

/-- Endpoint-derived metadata and prefix-dependent output assembly, with an explicit read set.
Coins may contain correlated finite retry tapes; preparation evaluates them deterministically. -/
structure EndpointContinuation (I H Coins Metadata Output : Type) (v : ℕ) where
  /-- Prepare all metadata from endpoints and fixed coins, without reading hidden starts. -/
  prepare : (I → Fin v → H) → Coins → Metadata
  /-- Materialize an output using the prepared metadata and chain-prefix values. -/
  materialize : Metadata → (I → Fin v → ℕ → H) → Output
  /-- Prefix positions on which materialization can depend. -/
  reads : Metadata → I → Fin v → ℕ → Prop
  /-- Equality on the declared read set preserves the materialized output. -/
  materialize_congr : ∀ metadata prefixes₁ prefixes₂,
    (∀ c i p, reads metadata c i p → prefixes₁ c i p = prefixes₂ c i p) →
      materialize metadata prefixes₁ = materialize metadata prefixes₂

/-- Equal endpoint tables and the same fixed coins yield identical metadata. -/
theorem EndpointContinuation.prepare_eq
    (ctx : EndpointContinuation I H Coins Metadata Output v)
    (left right : I → Fin v → H) (coins : Coins) (h : left = right) :
    ctx.prepare left coins = ctx.prepare right coins := congrArg (ctx.prepare · coins) h

/-- Advancing a splice preserves metadata and outputs whose selected reads lie past both cuts. -/
theorem EndpointContinuation.materialize_splice_advance [DecidableEq I]
    (ctx : EndpointContinuation I H Coins Metadata Output v)
    (family : ChainFamily I H v) (n : ℕ) (selected : I) (selectedChain : Fin v)
    (cut : ℕ) (answer : H) (starts : I → Fin v → H) (coins : Coins)
    (hn : cut + 2 ≤ n)
    (hsafe : ∀ c i p,
      ctx.reads (ctx.prepare (spliceEndpoints family n selected selectedChain cut answer starts)
        coins) c i p → c = selected → i = selectedChain → cut + 2 ≤ p) :
    ctx.materialize
      (ctx.prepare (spliceEndpoints family n selected selectedChain cut answer starts) coins)
      (spliceValue family selected selectedChain cut answer starts) =
    ctx.materialize
      (ctx.prepare (spliceEndpoints family n selected selectedChain (cut + 1)
        (family.chain selected selectedChain (cut + 1) 1 answer) starts) coins)
      (spliceValue family selected selectedChain (cut + 1)
        (family.chain selected selectedChain (cut + 1) 1 answer) starts) := by
  rw [← spliceEndpoints_advance family n selected selectedChain cut answer starts hn]
  apply ctx.materialize_congr
  intro c i p hread
  exact spliceValue_advance family selected selectedChain cut answer starts c i p
    (hsafe c i p hread)

/-- At zero cut, safe materialization is independent of the old selected start. -/
theorem EndpointContinuation.materialize_zero_start_update [DecidableEq I]
    (ctx : EndpointContinuation I H Coins Metadata Output v)
    (family : ChainFamily I H v) (n : ℕ) (selected : I) (selectedChain : Fin v)
    (answer : H) (starts : I → Fin v → H) (x : H) (coins : Coins) (hn : 0 < n)
    (hsafe : ∀ c i p,
      ctx.reads (ctx.prepare (spliceEndpoints family n selected selectedChain 0 answer starts)
        coins) c i p → c = selected → i = selectedChain → 0 < p) :
    ctx.materialize
      (ctx.prepare (spliceEndpoints family n selected selectedChain 0 answer
        (Function.update starts selected (Function.update (starts selected) selectedChain x)))
        coins)
      (spliceValue family selected selectedChain 0 answer
        (Function.update starts selected (Function.update (starts selected) selectedChain x))) =
    ctx.materialize
      (ctx.prepare (spliceEndpoints family n selected selectedChain 0 answer starts) coins)
      (spliceValue family selected selectedChain 0 answer starts) := by
  rw [spliceEndpoints_zero_start_update family n selected selectedChain answer starts x hn]
  apply ctx.materialize_congr
  intro c i p hread
  exact spliceValue_zero_start_update family selected selectedChain answer starts x c i p
    (hsafe c i p hread)

end GXMSS.Reductions.ChainContinuation
