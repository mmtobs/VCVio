/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.HashInstance
public import HashSig.GXMSS.Hypertree.Coordinates

/-!
# One common hash for a hypertree

Global component coordinates separate chain and Merkle tweaks across every layer and tree.
Restricting the common hash to one component gives the existing GXMSS hash interface.
Input embedding images may overlap; the two tweak families have disjoint images.
-/

public section

namespace GXMSS.Hypertree

/-- One tweakable hash with globally injective and separated forest coordinates. -/
structure HashInstance (PP T X H : Type) (S : Shape) where
  /-- Common tweakable hash and public-parameter sampler. -/
  thf : TweakableHash PP T X H
  /-- Embed one chain digest into the common input domain. -/
  digestInput : H ↪ X
  /-- Embed an ordered left/right digest pair into the common input domain. -/
  pairInput : (H × H) ↪ X
  /-- Embed a complete vector of chain endpoints into the common input domain. -/
  vectorInput : (Fin S.v → H) ↪ X
  /-- Injectively label every positive chain call in every component. -/
  chainTweak : ChainPosition S ↪ T
  /-- Injectively label the full finite Merkle rectangle in every component. -/
  treeTweak : (TreePosition S × Fin (S.h + 1) × Fin S.branching) ↪ T
  /-- The global chain and tree tweak images are disjoint. -/
  chain_ne_tree : ∀ c t, chainTweak c ≠ treeTweak t

namespace HashInstance

variable {PP T X H : Type} {S : Shape}

/-- Restrict the global hash coordinates to one component tree. -/
@[expose] def componentHash (P : HashInstance PP T X H S) (p : TreePosition S) :
    GXMSS.HashInstance PP T X H S.h S.w S.v where
  thf := P.thf
  digestInput := P.digestInput
  pairInput := P.pairInput
  vectorInput := P.vectorInput
  chainTweak :=
    ⟨fun c => P.chainTweak ((p, c.1), c.2), fun _ _ h =>
      congrArg (fun x : ChainPosition S => (x.1.2, x.2)) (P.chainTweak.injective h)⟩
  treeTweak :=
    ⟨fun t => P.treeTweak (p, t), fun _ _ h =>
      congrArg Prod.snd (P.treeTweak.injective h)⟩
  chain_ne_tree c t := P.chain_ne_tree ((p, c.1), c.2) (p, t)

/-- All components use the same tweakable hash, including its public-parameter sampler. -/
@[simp] theorem componentHash_thf (P : HashInstance PP T X H S) (p : TreePosition S) :
    (P.componentHash p).thf = P.thf := rfl

/-- Component digest inputs use the common embedding. -/
@[simp] theorem componentHash_digestInput (P : HashInstance PP T X H S)
    (p : TreePosition S) : (P.componentHash p).digestInput = P.digestInput := rfl

/-- Component ordered-pair inputs use the common embedding. -/
@[simp] theorem componentHash_pairInput (P : HashInstance PP T X H S)
    (p : TreePosition S) : (P.componentHash p).pairInput = P.pairInput := rfl

/-- Component endpoint-vector inputs use the common embedding. -/
@[simp] theorem componentHash_vectorInput (P : HashInstance PP T X H S)
    (p : TreePosition S) : (P.componentHash p).vectorInput = P.vectorInput := rfl

/-- A component chain tweak retains its full global one-time-key coordinate. -/
@[simp] theorem componentHash_chainTweak (P : HashInstance PP T X H S)
    (p : TreePosition S) (c : Fin (2 ^ S.h) × Fin S.v × Fin (2 ^ S.w - 1)) :
    (P.componentHash p).chainTweak c = P.chainTweak ((p, c.1), c.2) := rfl

/-- A component Merkle tweak retains its component coordinate and ordered rectangle address. -/
@[simp] theorem componentHash_treeTweak (P : HashInstance PP T X H S)
    (p : TreePosition S) (t : Fin (S.h + 1) × Fin (2 ^ S.h)) :
    (P.componentHash p).treeTweak t = P.treeTweak (p, t) := rfl

/-- Equal component chain tweaks force both component and local call equality. -/
theorem componentHash_chainTweak_eq_iff (P : HashInstance PP T X H S)
    (p q : TreePosition S)
    (c d : Fin (2 ^ S.h) × Fin S.v × Fin (2 ^ S.w - 1)) :
    (P.componentHash p).chainTweak c = (P.componentHash q).chainTweak d ↔
      p = q ∧ c = d := by
  constructor
  · intro h
    have he := P.chainTweak.injective h
    exact ⟨congrArg (fun x : ChainPosition S => x.1.1) he,
      congrArg (fun x : ChainPosition S => (x.1.2, x.2)) he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Equal component Merkle tweaks force both component and local address equality. -/
theorem componentHash_treeTweak_eq_iff (P : HashInstance PP T X H S)
    (p q : TreePosition S) (s t : Fin (S.h + 1) × Fin (2 ^ S.h)) :
    (P.componentHash p).treeTweak s = (P.componentHash q).treeTweak t ↔
      p = q ∧ s = t := by
  constructor
  · intro h
    have he := P.treeTweak.injective h
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- No chain tweak collides with a Merkle tweak, even in a different component. -/
theorem componentHash_chain_ne_tree (P : HashInstance PP T X H S)
    (p q : TreePosition S)
    (c : Fin (2 ^ S.h) × Fin S.v × Fin (2 ^ S.w - 1))
    (t : Fin (S.h + 1) × Fin (2 ^ S.h)) :
    (P.componentHash p).chainTweak c ≠ (P.componentHash q).treeTweak t :=
  P.chain_ne_tree ((p, c.1), c.2) (q, t)

end HashInstance

end GXMSS.Hypertree
