/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.HashInstance
public import HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation
import all HashSig.GXMSS.Security.Reductions.TargetRegistrationSimulation

/-!
# Global forest target ledgers

All component chains precede all component Merkle traversals. A fixed finite enumeration chooses
the component issue order, independently of the public hash seed. Each component retains the
existing positive-step chain order and left-subtree, right-subtree, parent Merkle order.
-/

public section

namespace GXMSS.Hypertree.Unforgeability

open GXMSS.Reductions TweakableHash

variable {PP T X H : Type} {S : Shape}

/-- A fixed seed-independent enumeration of every component exactly once. -/
@[expose] noncomputable def componentEnumeration (S : Shape) :
    Fin (treeCount S) ≃ TreePosition S := by
  let := Fintype.ofFinite (TreePosition S)
  have hc : Fintype.card (TreePosition S) = treeCount S := by
    simpa only [Nat.card_eq_fintype_card] using card_treePosition S
  exact (finCongr hc.symm).trans (Fintype.equivFin (TreePosition S)).symm

/-- Honest positive-step targets of one component, using full forest start coordinates. -/
@[expose] def componentChainTargets (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (p : TreePosition S) : List (T × X) :=
  endpointTargets (hash.componentHash p) pp (fun ep => starts (p, ep))

/-- Honest ordered Merkle targets of one component, using full forest endpoint coordinates. -/
@[expose] def componentMerkleTargets (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) (p : TreePosition S) : List (T × X) :=
  merkleTargets (hash.componentHash p) pp (fun ep => ends (p, ep))

/-- Every positive chain target in component-major, local-epoch-major, chain-major order. -/
@[expose] noncomputable def chainLedger (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) : List (T × X) :=
  (List.ofFn fun a : Fin (treeCount S) =>
    componentChainTargets hash pp starts (componentEnumeration S a)).flatten

/-- Every full Merkle traversal, in the same fixed component order as chain setup. -/
@[expose] noncomputable def merkleLedger (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) : List (T × X) :=
  (List.ofFn fun a : Fin (treeCount S) =>
    componentMerkleTargets hash pp ends (componentEnumeration S a)).flatten

/-- Complete setup issues all chain targets before all hashed leaves and internal nodes. -/
@[expose] noncomputable def setupLedger (hash : HashInstance PP T X H S) (pp : PP)
    (starts ends : OTSPosition S → Fin S.v → H) : List (T × X) :=
  chainLedger hash pp starts ++ merkleLedger hash pp ends

/-- Full forest chain setup has exactly one target for each positive chain position. -/
@[simp] theorem chainLedger_length (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) :
    (chainLedger hash pp starts).length = chainCount S := by
  simp [chainLedger, componentChainTargets, List.length_flatten, List.sum_ofFn,
    chainCount, otsCount, Shape.branching, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Full forest Merkle setup counts every hashed leaf and every internal node once. -/
@[simp] theorem merkleLedger_length (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) :
    (merkleLedger hash pp ends).length = treeCount S * (2 * S.branching - 1) := by
  simp [merkleLedger, componentMerkleTargets, List.length_flatten, List.sum_ofFn,
    Shape.branching, pow_succ, Nat.mul_comm]

/-- The complete actual setup ledger has the sharp chain-plus-Merkle length. -/
@[simp] theorem setupLedger_length (hash : HashInstance PP T X H S) (pp : PP)
    (starts ends : OTSPosition S → Fin S.v → H) :
    (setupLedger hash pp starts ends).length =
      chainCount S + treeCount S * (2 * S.branching - 1) := by
  simp [setupLedger]

/-- Each component's chain targets occur in the global chain ledger. -/
theorem componentChainTarget_mem_chainLedger (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (p : TreePosition S) {q : T × X}
    (hq : q ∈ componentChainTargets hash pp starts p) : q ∈ chainLedger hash pp starts := by
  apply List.mem_flatten.mpr
  refine ⟨componentChainTargets hash pp starts p, ?_, hq⟩
  exact List.mem_ofFn.mpr ⟨(componentEnumeration S).symm p, by simp⟩

/-- Each component's exact Merkle inputs occur in the global Merkle ledger. -/
theorem componentMerkleTarget_mem_merkleLedger (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) (p : TreePosition S) {q : T × X}
    (hq : q ∈ componentMerkleTargets hash pp ends p) : q ∈ merkleLedger hash pp ends := by
  apply List.mem_flatten.mpr
  refine ⟨componentMerkleTargets hash pp ends p, ?_, hq⟩
  exact List.mem_ofFn.mpr ⟨(componentEnumeration S).symm p, by simp⟩

/-- Every positive step is present with its exact honest chain input, not merely its tweak. -/
theorem chainTarget_mem_chainLedger (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (p : TreePosition S)
    (ep : Fin S.branching) (i : Fin S.v) (j : Fin (2 ^ S.w - 1)) :
    ((hash.componentHash p).chainTweak (ep, i, j),
      hash.digestInput ((hash.componentHash p).chain pp ep i 0 j.val (starts (p, ep) i))) ∈
        chainLedger hash pp starts :=
  componentChainTarget_mem_chainLedger hash pp starts p
    (chainTarget_mem_endpointTargets (hash.componentHash p) pp (fun ep => starts (p, ep)) ep i j)

/-- Every honest opening input is present globally, with the original leaf-first path and
ordered left/right child values retained by the component Merkle schedule. -/
theorem merkleOpeningTarget_mem_setupLedger (hash : HashInstance PP T X H S) (pp : PP)
    (starts ends : OTSPosition S → Fin S.v → H) (p : TreePosition S)
    (ep : Fin S.branching) (target : T × X)
    (hmem : target ∈ (hash.componentHash p).merkleOpeningQueries pp ep (ends (p, ep))
      ((hash.componentHash p).authPath pp (fun ep => ends (p, ep)) ep)) :
    target ∈ setupLedger hash pp starts ends :=
  List.mem_append_right _ (componentMerkleTarget_mem_merkleLedger hash pp ends p
    (merkleOpeningTarget_mem_merkleTargets (hash.componentHash p) pp
      (fun ep => ends (p, ep)) ep target hmem))

/-- Every global chain target retains its full component and positive-step address. -/
theorem chainLedger_tweak (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) {q : T × X}
    (hq : q ∈ chainLedger hash pp starts) :
    ∃ p ep i j, q.1 = (hash.componentHash p).chainTweak (ep, i, j) := by
  obtain ⟨block, hblock, hq⟩ := List.mem_flatten.mp hq
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hblock
  obtain ⟨ep, i, j, heq⟩ := endpointTarget_tweak _ _ _ hq
  exact ⟨componentEnumeration S a, ep, i, j, heq⟩

/-- Every global Merkle target retains its full component and finite rectangle address. -/
theorem merkleLedger_tweak (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) {q : T × X}
    (hq : q ∈ merkleLedger hash pp ends) :
    ∃ p level index, q.1 = (hash.componentHash p).treeTweak (level, index) := by
  obtain ⟨block, hblock, hq⟩ := List.mem_flatten.mp hq
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hblock
  obtain ⟨level, index, heq⟩ := merkleTarget_tweak _ _ _ hq
  exact ⟨componentEnumeration S a, level, index, heq⟩

/-- No positive chain tweak is repeated anywhere in the complete forest. -/
theorem componentChainTargets_disjoint (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (p p' : TreePosition S) (hpp' : p ≠ p') :
    ∀ q ∈ componentChainTargets hash pp starts p,
      ∀ r ∈ componentChainTargets hash pp starts p', q.1 ≠ r.1 := by
  intro q hq r hr heq
  obtain ⟨ep, i, j, hqeq⟩ := endpointTarget_tweak _ _ _ hq
  obtain ⟨ep', i', j', hreq⟩ := endpointTarget_tweak _ _ _ hr
  rw [hqeq, hreq] at heq
  exact hpp' ((hash.componentHash_chainTweak_eq_iff _ _ _ _).1 heq).1

/-- Merkle target blocks of distinct components have disjoint tweak images. -/
theorem componentMerkleTargets_disjoint (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) (p p' : TreePosition S) (hpp' : p ≠ p') :
    ∀ q ∈ componentMerkleTargets hash pp ends p,
      ∀ r ∈ componentMerkleTargets hash pp ends p', q.1 ≠ r.1 := by
  intro q hq r hr heq
  obtain ⟨level, index, hqeq⟩ := merkleTarget_tweak _ _ _ hq
  obtain ⟨level', index', hreq⟩ := merkleTarget_tweak _ _ _ hr
  rw [hqeq, hreq] at heq
  exact hpp' ((hash.componentHash_treeTweak_eq_iff _ _ _ _).1 heq).1

/-- No positive chain tweak is repeated anywhere in the complete forest. -/
theorem chainLedger_tweaks_nodup (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) :
    ((chainLedger hash pp starts).map Prod.fst).Nodup := by
  apply targets_flatten_ofFn_tweaks_nodup
  · intro a
    exact endpointTargets_tweaks_nodup _ _ _
  · intro a b hab
    exact componentChainTargets_disjoint hash pp starts _ _
      (fun hp => hab ((componentEnumeration S).injective hp))

/-- No tree tweak is repeated across the full forest Merkle traversal. -/
theorem merkleLedger_tweaks_nodup (hash : HashInstance PP T X H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) :
    ((merkleLedger hash pp ends).map Prod.fst).Nodup := by
  apply targets_flatten_ofFn_tweaks_nodup
  · intro a
    exact merkleTargets_tweaks_nodup _ _ _
  · intro a b hab
    exact componentMerkleTargets_disjoint hash pp ends _ _
      (fun hp => hab ((componentEnumeration S).injective hp))

/-- Chain and tree target families remain disjoint across all component boundaries. -/
theorem chainLedger_merkleLedger_disjoint (hash : HashInstance PP T X H S) (pp : PP)
    (starts ends : OTSPosition S → Fin S.v → H) :
    ∀ q ∈ chainLedger hash pp starts, ∀ r ∈ merkleLedger hash pp ends, q.1 ≠ r.1 := by
  intro q hq r hr
  obtain ⟨p, ep, i, j, hqeq⟩ := chainLedger_tweak hash pp starts hq
  obtain ⟨p', level, index, hreq⟩ := merkleLedger_tweak hash pp ends hr
  rw [hqeq, hreq]
  exact hash.componentHash_chain_ne_tree _ _ _ _

/-- The complete setup schedule never repeats any tweak. -/
theorem setupLedger_tweaks_nodup (hash : HashInstance PP T X H S) (pp : PP)
    (starts ends : OTSPosition S → Fin S.v → H) :
    ((setupLedger hash pp starts ends).map Prod.fst).Nodup := by
  rw [setupLedger, List.map_append, List.nodup_append]
  refine ⟨chainLedger_tweaks_nodup hash pp starts,
    merkleLedger_tweaks_nodup hash pp ends, ?_⟩
  intro t ht u hu htu
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
  exact chainLedger_merkleLedger_disjoint hash pp starts ends q hq r hr htu

/-- The common chain target capacity, with no component-guessing multiplier. -/
@[expose] def chainCapacity (S : Shape) : ℕ := otsCount S * S.v * 2 ^ S.w

/-- The common Merkle target capacity covers chain setup and all full-tree traversals. -/
@[expose] def merkleCapacity (S : Shape) : ℕ := 2 * otsCount S * S.v * 2 ^ S.w

/-- Positive-chain targets fit the inherited chain capacity, also at width zero. -/
theorem chainCount_le_capacity (S : Shape) : chainCount S ≤ chainCapacity S := by
  exact Nat.mul_le_mul_left (otsCount S * S.v) (Nat.sub_le _ _)

/-- A positive number of chains suffices for the global chain-plus-Merkle setup capacity. -/
theorem setupCount_le_capacity (S : Shape) (hv : 0 < S.v) :
    chainCount S + treeCount S * (2 * S.branching - 1) ≤ merkleCapacity S := by
  have hd : 0 < 2 ^ S.w := Nat.two_pow_pos S.w
  have hsplit : 2 ^ S.w = (2 ^ S.w - 1) + 1 := by omega
  have hchain : chainCount S ≤ 2 * chainCount S := by omega
  have htreeBound : treeCount S * (2 * S.branching - 1) ≤ 2 * otsCount S * S.v := by
    calc
      treeCount S * (2 * S.branching - 1) ≤ treeCount S * (2 * S.branching) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * otsCount S := by simp [otsCount]; ring
      _ ≤ 2 * otsCount S * S.v := Nat.le_mul_of_pos_right _ hv
  calc
    chainCount S + treeCount S * (2 * S.branching - 1) ≤
        2 * chainCount S + 2 * otsCount S * S.v := Nat.add_le_add hchain htreeBound
    _ = 2 * otsCount S * S.v * ((2 ^ S.w - 1) + 1) := by simp [chainCount]; ring
    _ = merkleCapacity S := by rw [← hsplit]; rfl

end GXMSS.Hypertree.Unforgeability
