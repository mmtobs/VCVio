/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Finite hypertree coordinates

Layers are numbered from the message-signing bottom layer to the single top tree. All trees
have a common height; a global epoch selects one tree and one local leaf in every layer.
The coordinate domains and their cardinalities also admit height zero.
-/

public section

namespace GXMSS.Hypertree

/-- Common parameters of a positive-depth hypertree. -/
structure Shape where
  /-- Number of layers. -/
  d : ℕ
  /-- Height of every component tree. -/
  h : ℕ
  /-- Width of each encoding digit. -/
  w : ℕ
  /-- Number of chains in each one-time signing key. -/
  v : ℕ
  /-- Every hypertree has at least one layer. -/
  d_pos : 0 < d
  deriving DecidableEq

namespace Shape

/-- Number of leaves in a component tree. -/
@[expose, reducible] def branching (S : Shape) : ℕ := 2 ^ S.h

/-- A component tree always has a leaf, including at height zero. -/
theorem branching_pos (S : Shape) : 0 < S.branching := by
  exact Nat.two_pow_pos S.h

/-- The global leaf capacity expressed using the common branching factor. -/
theorem branching_pow_depth (S : Shape) : S.branching ^ S.d = 2 ^ (S.d * S.h) := by
  simp [branching, ← pow_mul, Nat.mul_comm]

end Shape

/-- Global epochs are bounded by the full bottom-layer leaf capacity. -/
@[expose, reducible] def Epoch (S : Shape) := Fin (2 ^ (S.d * S.h))

/-- Tree indices in a bottom-up layer. -/
@[expose, reducible] def TreeIndex (S : Shape) (ell : Fin S.d) :=
  Fin (S.branching ^ (S.d - 1 - ell.val))

/-- A layer and an index of a component tree in that layer. -/
@[expose, reducible] def TreePosition (S : Shape) := (ell : Fin S.d) × TreeIndex S ell

/-- A component tree and one of its local one-time signing keys. -/
@[expose, reducible] def OTSPosition (S : Shape) := TreePosition S × Fin S.branching

/-- A positive chain call, with its full global one-time-key coordinate. -/
@[expose, reducible] def ChainPosition (S : Shape) :=
  OTSPosition S × Fin S.v × Fin (2 ^ S.w - 1)

instance (S : Shape) : Finite (Epoch S) := inferInstanceAs (Finite (Fin _))
instance (S : Shape) : DecidableEq (Epoch S) := inferInstanceAs (DecidableEq (Fin _))
instance (S : Shape) (ell : Fin S.d) : Finite (TreeIndex S ell) :=
  inferInstanceAs (Finite (Fin _))
instance (S : Shape) (ell : Fin S.d) : DecidableEq (TreeIndex S ell) :=
  inferInstanceAs (DecidableEq (Fin _))
instance (S : Shape) : Finite (TreePosition S) := inferInstanceAs (Finite (Sigma _))
instance (S : Shape) : DecidableEq (TreePosition S) := inferInstanceAs (DecidableEq (Sigma _))
instance (S : Shape) : Finite (OTSPosition S) := inferInstanceAs (Finite (_ × _))
instance (S : Shape) : DecidableEq (OTSPosition S) := inferInstanceAs (DecidableEq (_ × _))
instance (S : Shape) : Finite (ChainPosition S) := inferInstanceAs (Finite (_ × _))
instance (S : Shape) : DecidableEq (ChainPosition S) := inferInstanceAs (DecidableEq (_ × _))

/-- Tree coordinates agree when their layers and natural tree indices agree. -/
@[ext] theorem treePosition_ext {S : Shape} {p q : TreePosition S}
    (hl : p.1 = q.1) (hi : p.2.val = q.2.val) : p = q := by
  rcases p with ⟨ell, i⟩
  rcases q with ⟨ell', i'⟩
  cases hl
  exact congrArg (Sigma.mk ell) (Fin.ext hi)

/-- Decompose a global epoch into a component tree and local leaf at a chosen layer. -/
@[expose] def positionAt (S : Shape) (ep : Epoch S) (ell : Fin S.d) : OTSPosition S :=
  (⟨ell, ⟨ep.val / S.branching ^ (ell.val + 1), by
    have he : ep.val < S.branching ^ S.d := by
      rw [S.branching_pow_depth]
      exact ep.isLt
    apply (Nat.div_lt_iff_lt_mul (pow_pos S.branching_pos _)).2
    have hs : S.d - 1 - ell.val + (ell.val + 1) = S.d := by omega
    simpa [← pow_add, hs] using he⟩⟩,
    ⟨ep.val / S.branching ^ ell.val % S.branching,
      Nat.mod_lt _ S.branching_pos⟩)

/-- The selected component lies in the requested layer. -/
@[simp] theorem positionAt_layer (S : Shape) (ep : Epoch S) (ell : Fin S.d) :
    (positionAt S ep ell).1.1 = ell := rfl

/-- The component tree index is the quotient above the selected layer's leaf digit. -/
theorem positionAt_tree_val (S : Shape) (ep : Epoch S) (ell : Fin S.d) :
    (positionAt S ep ell).1.2.val = ep.val / S.branching ^ (ell.val + 1) := rfl

/-- The local leaf is the selected base-branching digit of the epoch. -/
theorem positionAt_leaf_val (S : Shape) (ep : Epoch S) (ell : Fin S.d) :
    (positionAt S ep ell).2.val = ep.val / S.branching ^ ell.val % S.branching := rfl

/-- The component tree and leaf recover the epoch quotient at the selected layer. -/
theorem positionAt_recompose (S : Shape) (ep : Epoch S) (ell : Fin S.d) :
    (positionAt S ep ell).1.2.val * S.branching + (positionAt S ep ell).2.val =
      ep.val / S.branching ^ ell.val := by
  have h := Nat.div_add_mod (ep.val / S.branching ^ ell.val) S.branching
  simpa only [positionAt, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using h

/-- Bottom-layer coordinates recover the full legal epoch without wrapping. -/
theorem positionAt_bottom_recompose (S : Shape) (ep : Epoch S) :
    (positionAt S ep ⟨0, S.d_pos⟩).1.2.val * S.branching +
      (positionAt S ep ⟨0, S.d_pos⟩).2.val = ep.val := by
  simpa using positionAt_recompose S ep ⟨0, S.d_pos⟩

/-- Distinct global epochs select distinct bottom-layer signing keys. -/
theorem positionAt_bottom_injective (S : Shape) :
    Function.Injective (fun ep : Epoch S => positionAt S ep ⟨0, S.d_pos⟩) := by
  intro ep eq hep
  apply Fin.ext
  have h := congrArg (fun p : OTSPosition S => p.1.2.val * S.branching + p.2.val) hep
  exact (positionAt_bottom_recompose S ep).symm.trans
    (h.trans (positionAt_bottom_recompose S eq))

/-- The one-time key in the next layer that certifies a non-top component's root. -/
@[expose] def parent (S : Shape) (p : TreePosition S) (hp : p.1.val + 1 < S.d) :
    OTSPosition S :=
  (⟨⟨p.1.val + 1, hp⟩, ⟨p.2.val / S.branching, by
    apply (Nat.div_lt_iff_lt_mul S.branching_pos).2
    have hs : S.d - 1 - p.1.val = (S.d - 1 - (p.1.val + 1)) + 1 := by omega
    simp [← pow_succ, ← hs]⟩⟩,
    ⟨p.2.val % S.branching, Nat.mod_lt _ S.branching_pos⟩)

/-- Parent certificates occur exactly one layer above their child trees. -/
theorem parent_layer_val (S : Shape) (p : TreePosition S) (hp : p.1.val + 1 < S.d) :
    (parent S p hp).1.1.val = p.1.val + 1 := rfl

/-- The parent tree is the quotient of the child tree index. -/
theorem parent_tree_val (S : Shape) (p : TreePosition S) (hp : p.1.val + 1 < S.d) :
    (parent S p hp).1.2.val = p.2.val / S.branching := rfl

/-- The parent signing leaf is the remainder of the child tree index. -/
theorem parent_leaf_val (S : Shape) (p : TreePosition S) (hp : p.1.val + 1 < S.d) :
    (parent S p hp).2.val = p.2.val % S.branching := rfl

/-- The parent coordinate determines the child tree index without loss. -/
theorem parent_recompose (S : Shape) (p : TreePosition S) (hp : p.1.val + 1 < S.d) :
    (parent S p hp).1.2.val * S.branching + (parent S p hp).2.val = p.2.val := by
  simpa only [parent, Nat.mul_comm] using Nat.div_add_mod p.2.val S.branching

/-- Adjacent epoch decompositions select the parent certificate of the lower component. -/
theorem parent_positionAt (S : Shape) (ep : Epoch S) (ell : Fin S.d)
    (hell : ell.val + 1 < S.d) :
    parent S (positionAt S ep ell).1 hell = positionAt S ep ⟨ell.val + 1, hell⟩ := by
  apply Prod.ext
  · apply treePosition_ext
    · rfl
    · dsimp [parent, positionAt]
      simp only [Nat.div_div_eq_div_mul, pow_succ]
  · rfl

/-- The unique top-layer component tree. -/
@[expose] def topTree (S : Shape) : TreePosition S :=
  ⟨⟨S.d - 1, by have := S.d_pos; omega⟩, ⟨0, Nat.pow_pos S.branching_pos⟩⟩

/-- Every top-layer component is the canonical top tree. -/
theorem eq_topTree_iff (S : Shape) (p : TreePosition S) :
    p = topTree S ↔ p.1.val = S.d - 1 := by
  constructor
  · rintro rfl
    rfl
  · intro hp
    apply treePosition_ext (Fin.ext hp)
    have hs : S.branching ^ (S.d - 1 - p.1.val) = 1 := by
      rw [hp, Nat.sub_self, pow_zero]
    have hi := lt_of_lt_of_eq p.2.isLt hs
    change p.2.val = 0
    omega

/-- The epoch decomposition always selects the unique component at the top layer. -/
theorem positionAt_topTree (S : Shape) (ep : Epoch S) :
    (positionAt S ep ⟨S.d - 1, by have := S.d_pos; omega⟩).1 = topTree S := by
  apply (eq_topTree_iff S _).2
  rfl

/-- One-time signing keys above the bottom layer certify fixed child roots. -/
@[expose, reducible] def UpperPosition (S : Shape) := {p : OTSPosition S // p.1.1.val ≠ 0}

instance (S : Shape) : Finite (UpperPosition S) := inferInstanceAs (Finite (Subtype _))
instance (S : Shape) : DecidableEq (UpperPosition S) :=
  inferInstanceAs (DecidableEq (Subtype _))

/-- The child tree whose root is certified by an upper-layer signing key. -/
@[expose] def childTree (S : Shape) (p : UpperPosition S) : TreePosition S :=
  ⟨⟨p.val.1.1.val - 1, by have := p.val.1.1.isLt; omega⟩,
    ⟨p.val.1.2.val * S.branching + p.val.2.val, by
      have hs : S.d - 1 - (p.val.1.1.val - 1) =
          (S.d - 1 - p.val.1.1.val) + 1 := by
        have := p.property
        have := p.val.1.1.isLt
        omega
      rw [hs, pow_succ]
      calc
        p.val.1.2.val * S.branching + p.val.2.val <
            p.val.1.2.val * S.branching + S.branching :=
          Nat.add_lt_add_left p.val.2.isLt _
        _ = (p.val.1.2.val + 1) * S.branching := by ring
        _ ≤ S.branching ^ (S.d - 1 - p.val.1.1.val) * S.branching :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt p.val.1.2.isLt)⟩⟩

/-- A child lies immediately below the key certifying its root. -/
theorem childTree_layer_val (S : Shape) (p : UpperPosition S) :
    (childTree S p).1.val = p.val.1.1.val - 1 := rfl

/-- The child-tree index combines the parent's tree and leaf digits. -/
theorem childTree_index_val (S : Shape) (p : UpperPosition S) :
    (childTree S p).2.val = p.val.1.2.val * S.branching + p.val.2.val := rfl

/-- The child of an upper signing key is below the top layer. -/
theorem childTree_not_top (S : Shape) (p : UpperPosition S) :
    (childTree S p).1.val + 1 < S.d := by
  have := p.val.1.1.isLt
  have := p.property
  dsimp [childTree]
  omega

/-- The parent coordinate of a child tree recovers its upper signing key. -/
theorem parent_childTree (S : Shape) (p : UpperPosition S) :
    parent S (childTree S p) (childTree_not_top S p) = p.val := by
  apply Prod.ext
  · apply treePosition_ext
    · apply Fin.ext
      have := p.property
      dsimp [parent, childTree]
      omega
    · change (p.val.1.2.val * S.branching + p.val.2.val) / S.branching = p.val.1.2.val
      have h := Nat.add_mul_div_left p.val.2.val p.val.1.2.val S.branching_pos
      rw [Nat.div_eq_of_lt p.val.2.isLt, Nat.zero_add] at h
      simpa only [Nat.add_comm, Nat.mul_comm] using h
  · apply Fin.ext
    dsimp [parent, childTree]
    simp [Nat.add_mod, Nat.mod_eq_of_lt p.val.2.isLt]

/-- A non-top tree determines its parent certificate coordinate in the upper layers. -/
@[expose] def upperParent (S : Shape) (p : TreePosition S)
    (hp : p.1.val + 1 < S.d) : UpperPosition S :=
  ⟨parent S p hp, by dsimp [parent]; omega⟩

/-- The child of a tree's parent certificate is the original tree. -/
theorem childTree_upperParent (S : Shape) (p : TreePosition S)
    (hp : p.1.val + 1 < S.d) : childTree S (upperParent S p hp) = p := by
  apply treePosition_ext
  · apply Fin.ext
    simp [childTree, upperParent, parent]
  · exact parent_recompose S p hp

/-- The child certified at an upper epoch coordinate is the preceding layer's component. -/
theorem childTree_positionAt (S : Shape) (ep : Epoch S) (ell : Fin S.d)
    (hell : ell.val ≠ 0) :
    childTree S ⟨positionAt S ep ell, by simpa only [positionAt_layer] using hell⟩ =
      (positionAt S ep ⟨ell.val - 1, by have := ell.isLt; omega⟩).1 := by
  apply treePosition_ext
  · rfl
  · have hs : ell.val - 1 + 1 = ell.val := by omega
    change (positionAt S ep ell).1.2.val * S.branching + (positionAt S ep ell).2.val =
      ep.val / S.branching ^ (ell.val - 1 + 1)
    rw [hs]
    exact positionAt_recompose S ep ell

/-- Number of component trees over all bottom-up layers. -/
@[expose] def treeCount (S : Shape) : ℕ :=
  ∑ ell : Fin S.d, S.branching ^ (S.d - 1 - ell.val)

/-- Number of one-time signing keys in all component trees. -/
@[expose] def otsCount (S : Shape) : ℕ := S.branching * treeCount S

/-- Number of fixed upper certificates. -/
@[expose] def upperCount (S : Shape) : ℕ := treeCount S - 1

/-- Number of positive chain calls in the full forest. -/
@[expose] def chainCount (S : Shape) : ℕ := otsCount S * S.v * (2 ^ S.w - 1)

/-- Reversing the layer order gives the ordinary finite geometric sum. -/
theorem treeCount_eq_sum_range (S : Shape) :
    treeCount S = ∑ i ∈ Finset.range S.d, S.branching ^ i := by
  rw [treeCount, Fin.sum_univ_eq_sum_range (fun i => S.branching ^ (S.d - 1 - i))]
  exact Finset.sum_range_reflect (fun i => S.branching ^ i) S.d

/-- A positive-depth hypertree contains its top component. -/
theorem treeCount_pos (S : Shape) : 0 < treeCount S := by
  rw [treeCount_eq_sum_range]
  have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.range S.d) =>
    Nat.zero_le (S.branching ^ i)) (Finset.mem_range.mpr S.d_pos)
  exact lt_of_lt_of_le Nat.zero_lt_one (by simpa using h)

/-- Counting the leaves of all components by their layers. -/
theorem otsCount_eq_sum_layers (S : Shape) :
    otsCount S = ∑ ell : Fin S.d, S.branching ^ (S.d - ell.val) := by
  rw [otsCount, treeCount, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  rw [← pow_succ']
  congr 1
  have := ell.isLt
  omega

/-- The geometric forest identity counts leaves as bottom epochs plus upper certificates. -/
theorem otsCount_add_one (S : Shape) :
    otsCount S + 1 = treeCount S + S.branching ^ S.d := by
  have hb : 1 ≤ S.branching := S.branching_pos
  have hg := geom_sum_mul_add (S.branching - 1) S.d
  rw [Nat.sub_add_cancel hb, ← treeCount_eq_sum_range] at hg
  have hm : treeCount S * (S.branching - 1) + treeCount S = otsCount S := by
    calc
      treeCount S * (S.branching - 1) + treeCount S =
          treeCount S * ((S.branching - 1) + 1) := by ring
      _ = otsCount S := by rw [Nat.sub_add_cancel hb, otsCount, Nat.mul_comm]
  omega

/-- Removing the bottom-epoch slots leaves exactly one certificate per non-top tree. -/
theorem upperCount_eq_otsCount_sub_epochs (S : Shape) :
    upperCount S = otsCount S - S.branching ^ S.d := by
  have := otsCount_add_one S
  have := treeCount_pos S
  dsimp [upperCount]
  omega

/-- The finite dependent coordinate domain has exactly one element per component tree. -/
theorem card_treePosition (S : Shape) : Nat.card (TreePosition S) = treeCount S := by
  change Nat.card (Sigma (TreeIndex S)) = _
  rw [Nat.card_sigma]
  simp only [TreeIndex, Nat.card_fin, treeCount]

/-- The finite one-time-key domain has the forest leaf cardinality. -/
theorem card_otsPosition (S : Shape) : Nat.card (OTSPosition S) = otsCount S := by
  change Nat.card (TreePosition S × Fin S.branching) = _
  rw [Nat.card_prod, card_treePosition, Nat.card_fin, otsCount, Nat.mul_comm]

/-- The finite positive-chain domain has exactly the full forest chain-call count. -/
theorem card_chainPosition (S : Shape) : Nat.card (ChainPosition S) = chainCount S := by
  simp only [ChainPosition, OTSPosition, Nat.card_prod, card_treePosition, Nat.card_fin,
    chainCount, otsCount, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Bottom-layer signing keys correspond to all legal global epochs. -/
private def bottomPositionEquiv (S : Shape) :
    {p : OTSPosition S // p.1.1.val = 0} ≃
      Fin (S.branching ^ (S.d - 1)) × Fin S.branching where
  toFun p := (⟨p.val.1.2.val, by
    have hi := p.val.1.2.isLt
    simpa only [p.property, Nat.sub_zero] using hi⟩, p.val.2)
  invFun p := ⟨(⟨⟨0, S.d_pos⟩, p.1⟩, p.2), rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply treePosition_ext
      · exact Fin.ext p.property.symm
      · rfl
    · rfl
  right_inv p := rfl

/-- The bottom signing-key domain has the full bottom epoch cardinality. -/
theorem card_bottomPosition (S : Shape) :
    Nat.card {p : OTSPosition S // p.1.1.val = 0} = S.branching ^ S.d := by
  rw [Nat.card_congr (bottomPositionEquiv S), Nat.card_prod, Nat.card_fin, Nat.card_fin,
    ← pow_succ, Nat.sub_add_cancel S.d_pos]

/-- Upper certificate coordinates have exactly the non-top component-tree cardinality. -/
theorem card_upperPosition (S : Shape) : Nat.card (UpperPosition S) = upperCount S := by
  let := Fintype.ofFinite (OTSPosition S)
  rw [upperCount_eq_otsCount_sub_epochs, ← card_otsPosition, ← card_bottomPosition]
  simpa only [UpperPosition, Nat.card_eq_fintype_card] using
    Fintype.card_subtype_compl (fun p : OTSPosition S => p.1.1.val = 0)

/-- At height zero each layer consists of a single one-leaf component. -/
theorem treeCount_height_zero (S : Shape) (hh : S.h = 0) : treeCount S = S.d := by
  simp [treeCount, Shape.branching, hh]

/-- At depth one only the single top component is present. -/
theorem treeCount_depth_one (S : Shape) (hd : S.d = 1) : treeCount S = 1 := by
  rw [treeCount_eq_sum_range, hd]
  simp

end GXMSS.Hypertree
