/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.HashInstance
public import HashSig.GXMSS.Chain
public import HashSig.GXMSS.Merkle
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Hypertree coordinate consumers

Small independently calculated coordinates distinguish bottom-up layer numbering, tree and leaf
digits, and parent certificates. The hash consumers exercise the existing chain and Merkle APIs
through the global adapter and check the standard transitive axiom boundary.
-/

public section

namespace GXMSS.Hypertree.CoordinatesProbe

/-- Three binary layers with two width-two chains per signing key. -/
@[expose] def threeLayers : Shape := ⟨3, 1, 2, 2, by decide⟩

/-- Epoch five is binary 101, so its bottom tree is two and its local leaf is one. -/
theorem bottom_digit :
    let p := positionAt threeLayers ⟨5, by decide⟩ ⟨0, by decide⟩
    p.1.2.val = 2 ∧ p.2.val = 1 := by decide

/-- The middle layer at epoch five uses tree one and leaf zero. -/
theorem middle_digit :
    let p := positionAt threeLayers ⟨5, by decide⟩ ⟨1, by decide⟩
    p.1.2.val = 1 ∧ p.2.val = 0 := by decide

/-- The top layer at epoch five uses the unique tree and leaf one. -/
theorem top_digit :
    let p := positionAt threeLayers ⟨5, by decide⟩ ⟨2, by decide⟩
    p.1.2.val = 0 ∧ p.2.val = 1 := by decide

/-- Seven component trees have fourteen signing keys, six upper certificates and 84 chain calls. -/
theorem three_layer_counts :
    treeCount threeLayers = 7 ∧ otsCount threeLayers = 14 ∧
      upperCount threeLayers = 6 ∧ chainCount threeLayers = 84 := by decide

/-- A three-layer height-zero forest still contains three hashed leaves and two certificates. -/
theorem height_zero_counts :
    let S : Shape := ⟨3, 0, 1, 2, by decide⟩
    treeCount S = 3 ∧ otsCount S = 3 ∧ upperCount S = 2 ∧ chainCount S = 6 := by decide

/-- At depth one there are no upper certificate slots. -/
theorem depth_one_counts :
    let S : Shape := ⟨1, 2, 1, 2, by decide⟩
    treeCount S = 1 ∧ otsCount S = 4 ∧ upperCount S = 0 ∧ chainCount S = 8 := by decide

/-- The certificate of the middle-layer tree at epoch five is the top layer's leaf one. -/
theorem parent_digits :
    let p := parent threeLayers
      (positionAt threeLayers ⟨5, by decide⟩ ⟨1, by decide⟩).1 (by decide)
    p.1.1.val = 2 ∧ p.1.2.val = 0 ∧ p.2.val = 1 := by decide

/-- Three layers of height three, with independently calculated base-eight coordinates. -/
@[expose] def heightThree : Shape := ⟨3, 3, 2, 2, by decide⟩

/-- Epoch 345 has base-eight digits 531 from top to bottom. -/
theorem height_three_digits :
    let ep : Epoch heightThree := ⟨345, by decide⟩
    let p₀ := positionAt heightThree ep ⟨0, by decide⟩
    let p₁ := positionAt heightThree ep ⟨1, by decide⟩
    let p₂ := positionAt heightThree ep ⟨2, by decide⟩
    p₀.1.2.val = 43 ∧ p₀.2.val = 1 ∧ p₁.1.2.val = 5 ∧ p₁.2.val = 3 ∧
      p₂.1.2.val = 0 ∧ p₂.2.val = 5 := by decide

/-- Symbolic layer sums give the independently calculated height-three forest counts. -/
theorem height_three_counts :
    treeCount heightThree = 73 ∧ otsCount heightThree = 584 ∧
      upperCount heightThree = 72 ∧ chainCount heightThree = 3504 := by decide

/-- At height three, odd/even/odd climb steps retain left/right orientation and leaf-first paths. -/
theorem height_three_path_orientation :
    PerfectMerkleTree.climb (fun _ _ (left right : ℕ) => 100 * left + right)
      5 5 [4, 607, 303] = 71407 := by decide

/-- Reversing that authentication path does not reconstruct the independently calculated root. -/
theorem height_three_reversed_path :
    PerfectMerkleTree.climb (fun _ _ (left right : ℕ) => 100 * left + right)
      5 5 [303, 607, 4] ≠ 71407 := by decide

variable {PP T X H : Type} {S : Shape}

/-- Global separation prevents chain-tweak reuse across component trees. -/
theorem different_components_chain (P : HashInstance PP T X H S)
    (p q : TreePosition S) (hpq : p ≠ q)
    (c d : Fin (2 ^ S.h) × Fin S.v × Fin (2 ^ S.w - 1)) :
    (P.componentHash p).chainTweak c ≠ (P.componentHash q).chainTweak d := by
  intro h
  exact hpq ((P.componentHash_chainTweak_eq_iff p q c d).1 h).1

/-- Global separation prevents Merkle-tweak reuse across component trees. -/
theorem different_components_tree (P : HashInstance PP T X H S)
    (p q : TreePosition S) (hpq : p ≠ q)
    (s t : Fin (S.h + 1) × Fin (2 ^ S.h)) :
    (P.componentHash p).treeTweak s ≠ (P.componentHash q).treeTweak t := by
  intro h
  exact hpq ((P.componentHash_treeTweak_eq_iff p q s t).1 h).1

/-- The first existing GXMSS chain call has its full global positive-step coordinate. -/
theorem component_chain_first (P : HashInstance PP T X H S) (p : TreePosition S)
    (pp : PP) (e : Fin (2 ^ S.h)) (i : Fin S.v) (x : H) (hw : 1 ≤ 2 ^ S.w - 1) :
    (P.componentHash p).chain pp e i 0 1 x = P.thf.eval pp
      (P.chainTweak ((p, e), i, ⟨0, by omega⟩)) (P.digestInput x) := by
  simpa using (P.componentHash p).chain_succ pp e i 0 0 x hw

/-- Component endpoint vectors are hashed even when the component height is zero. -/
theorem component_leaf_hash (P : HashInstance PP T X H S) (p : TreePosition S)
    (pp : PP) (e : Fin (2 ^ S.h)) (xs : Fin S.v → H) :
    (P.componentHash p).leafHash pp e xs =
      P.thf.eval pp (P.treeTweak (p, 0, e)) (P.vectorInput xs) := rfl

/-- Existing leaf-first authentication paths reconstruct each globally addressed component. -/
theorem component_auth_path (P : HashInstance PP T X H S) (p : TreePosition S)
    (pp : PP) (xs : Fin (2 ^ S.h) → Fin S.v → H) (e : Fin (2 ^ S.h)) :
    (P.componentHash p).recoverRoot pp e (xs e) ((P.componentHash p).authPath pp xs e) =
      (P.componentHash p).merkleRoot pp xs :=
  (P.componentHash p).recoverRoot_authPath pp xs e

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``positionAt, ``positionAt_recompose, ``positionAt_bottom_injective,
    ``parent_positionAt, ``parent_childTree, ``childTree_upperParent, ``childTree_positionAt,
    ``card_treePosition, ``card_otsPosition, ``card_upperPosition, ``card_chainPosition,
    ``HashInstance.componentHash, ``HashInstance.componentHash_chainTweak_eq_iff,
    ``HashInstance.componentHash_treeTweak_eq_iff, ``HashInstance.componentHash_chain_ne_tree,
    ``bottom_digit, ``middle_digit, ``top_digit, ``three_layer_counts, ``height_zero_counts,
    ``depth_one_counts, ``parent_digits, ``component_chain_first, ``component_leaf_hash,
    ``component_auth_path, ``height_three_digits, ``height_three_counts,
    ``height_three_path_orientation, ``height_three_reversed_path]

run_cmd Lean.Elab.Command.liftTermElabM do
  let modules := #[`HashSig.GXMSS.Hypertree.Coordinates, `HashSig.GXMSS.Hypertree.HashInstance]
  let endpoints := #[(``card_upperPosition, `HashSig.GXMSS.Hypertree.Coordinates),
    (``childTree_positionAt, `HashSig.GXMSS.Hypertree.Coordinates),
    (``HashInstance.componentHash_chainTweak_eq_iff, `HashSig.GXMSS.Hypertree.HashInstance),
    (``HashInstance.componentHash_treeTweak_eq_iff, `HashSig.GXMSS.Hypertree.HashInstance)]
  let definitions := #[(``positionAt, `HashSig.GXMSS.Hypertree.Coordinates),
    (``HashInstance.componentHash, `HashSig.GXMSS.Hypertree.HashInstance)]
  GXMSS.Test.TrustAudit.check modules endpoints #[] definitions

end GXMSS.Hypertree.CoordinatesProbe
