/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Completeness
import all HashSig.GXMSS.Hypertree.Scheme
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
public import HashSig.GXMSS.Security.Hypertree.Reductions.TargetRegistration
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses

/-!
# Post-forgery forest witnesses

The top-down walk selects a component after seeing the complete forgery. It descends through an
upper layer only when its recovered child root and complete signature equal that coordinate's
fixed certificate. Exhausted and undisclosed private certificates are compared without omission.
-/

public section

namespace GXMSS.Hypertree.Unforgeability

open Encoding GXMSS.Security

/-- An actual component of the candidate signature, with its complete message fibre. -/
structure ComponentCandidate (M R H : Type) (S : Shape) where
  /-- Full component and local leaf coordinate. -/
  position : OTSPosition S
  /-- The application message or recovered child root supplied at that coordinate. -/
  message : Message S M H position
  /-- The candidate's complete component signature. -/
  signature : GXMSS.Signature R H S.h S.v

variable {PP T X H M R Coins : Type} {S : Shape}

/-- Read a candidate component with the exact message supplied by bottom-up verification. -/
@[expose] def candidateAt? (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP) (ep : Epoch S) (msg : M)
    (sig : Signature R H S) : (layer : ℕ) → layer < S.d → Option (ComponentCandidate M R H S)
  | 0, _ => some ⟨bottomPosition S ep, bottomMessage ep msg, sig.bottom⟩
  | layer + 1, hlayer => do
      let child ← recoverThrough hash family pp ep msg sig layer (by omega)
      let i : Fin (S.d - 1) := ⟨layer, by omega⟩
      pure ⟨(upperPositionAt S ep i).1, internalMessage (upperPositionAt S ep i) child,
        sig.upper i⟩

/-- Every returned component has the global epoch's exact coordinate at its selected layer. -/
theorem candidateAt?_position (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP) (ep : Epoch S) (msg : M)
    (sig : Signature R H S) (layer : ℕ) (hlayer : layer < S.d)
    (candidate : ComponentCandidate M R H S)
    (hc : candidateAt? hash family pp ep msg sig layer hlayer = some candidate) :
    candidate.position = positionAt S ep ⟨layer, hlayer⟩ := by
  cases layer with
  | zero => cases Option.some.inj hc; rfl
  | succ layer =>
      cases hchild : recoverThrough hash family pp ep msg sig layer (by omega) with
      | none => simp [candidateAt?, hchild] at hc
      | some child =>
          have heq : candidate = ⟨(upperPositionAt S ep ⟨layer, by omega⟩).1,
              internalMessage (upperPositionAt S ep ⟨layer, by omega⟩) child,
              sig.upper ⟨layer, by omega⟩⟩ := by
            simpa [candidateAt?, hchild] using hc.symm
          subst candidate
          rfl

/-- Reading the actual component and recovering it is exactly the existing bounded verifier. -/
theorem recoverThrough_eq_candidateAt (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP) (ep : Epoch S) (msg : M)
    (sig : Signature R H S) (layer : ℕ) (hlayer : layer < S.d) :
    recoverThrough hash family pp ep msg sig layer hlayer =
      (candidateAt? hash family pp ep msg sig layer hlayer).bind fun candidate =>
        recoverComponent hash family pp candidate.position candidate.message
          candidate.signature := by
  cases layer <;> simp [recoverThrough, candidateAt?, Option.bind_assoc]

/-- Successful bounded recovery supplies an actual component with that same recovered root. -/
theorem candidateAt?_of_recoverThrough (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP) (ep : Epoch S) (msg : M)
    (sig : Signature R H S) (layer : ℕ) (hlayer : layer < S.d) (root : H)
    (hroot : recoverThrough hash family pp ep msg sig layer hlayer = some root) :
    ∃ candidate, candidateAt? hash family pp ep msg sig layer hlayer = some candidate ∧
      recoverComponent hash family pp candidate.position candidate.message candidate.signature =
        some root := by
  rw [recoverThrough_eq_candidateAt] at hroot
  exact Option.bind_eq_some_iff.mp hroot

/-- Re-encoding success and the actual forged endpoint vector follow from component recovery. -/
theorem word_of_recoverComponent (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP)
    (candidate : ComponentCandidate M R H S) (root : H)
    (hroot : recoverComponent hash family pp candidate.position candidate.message
      candidate.signature = some root) :
    ∃ word : Codeword S.v (2 ^ S.w),
      family.value candidate.position pp candidate.message candidate.signature.randomizer =
        some word ∧
      (hash.componentHash candidate.position.1).recoverRoot pp candidate.position.2
        (fun i => (hash.componentHash candidate.position.1).chain pp candidate.position.2 i (word i)
          (2 ^ S.w - 1 - (word i).val) (candidate.signature.ots i))
        candidate.signature.path = root := by
  cases hword : family.value candidate.position pp candidate.message
      candidate.signature.randomizer with
  | none => simp [recoverComponent, hword] at hroot
  | some word =>
      exact ⟨word, rfl, by simpa [recoverComponent, hword] using hroot⟩

/-- An upper component is aligned only when its message and full fixed certificate both agree. -/
@[expose, reducible] def UpperAligned (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M)
    (sig : Signature R H S) (i : Fin (S.d - 1)) : Prop :=
  recoverThrough hash family pp ep msg sig i.val (by have := i.isLt; omega) =
      some (componentRoot hash pp ends (childTree S (upperPositionAt S ep i))) ∧
    references (upperPositionAt S ep i) = some (sig.upper i)

/-- Search down from a bounded layer, stopping at its first altered message/certificate pair. -/
@[expose] def selectLayer [DecidableEq H] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) :
    (layer : ℕ) → layer < S.d → Fin S.d
  | 0, hlayer => ⟨0, hlayer⟩
  | layer + 1, hlayer =>
      if UpperAligned hash family pp ends references ep msg sig ⟨layer, by omega⟩ then
        selectLayer hash family pp ends references ep msg sig layer (by omega)
      else ⟨layer + 1, hlayer⟩

/-- The complete post-forgery selector starts at the top layer and never guesses a component. -/
@[expose] def selectedLayer [DecidableEq H] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) :
    Fin S.d := selectLayer hash family pp ends references ep msg sig (S.d - 1)
      (by have := S.d_pos; omega)

/-- The selected component never lies above the layer where the walk began. -/
theorem selectLayer_le [DecidableEq H] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) (layer : ℕ) (hlayer : layer < S.d) :
    (selectLayer hash family pp ends references ep msg sig layer hlayer).val ≤ layer := by
  induction layer with
  | zero => rfl
  | succ layer ih =>
      by_cases ha : UpperAligned hash family pp ends references ep msg sig ⟨layer, by omega⟩
      · simp only [selectLayer, ite_eq_left ha]
        exact (ih (by omega)).trans (Nat.le_succ _)
      · simp only [selectLayer, ite_eq_right ha]
        exact le_rfl

/-- A bound component root remains bound when the walk descends through an aligned certificate. -/
theorem selectLayer_root [DecidableEq H] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) (layer : ℕ) (hlayer : layer < S.d)
    (hroot : recoverThrough hash family pp ep msg sig layer hlayer =
      some (componentRoot hash pp ends (positionAt S ep ⟨layer, hlayer⟩).1)) :
    let selected := selectLayer hash family pp ends references ep msg sig layer hlayer
    recoverThrough hash family pp ep msg sig selected.val selected.isLt =
      some (componentRoot hash pp ends (positionAt S ep selected).1) := by
  induction layer with
  | zero => exact hroot
  | succ layer ih =>
      by_cases ha : UpperAligned hash family pp ends references ep msg sig ⟨layer, by omega⟩
      · simp only [selectLayer, ite_eq_left ha]
        apply ih (by omega)
        have hc : childTree S (upperPositionAt S ep ⟨layer, by omega⟩) =
            (positionAt S ep ⟨layer, by omega⟩).1 := by
          simpa [upperPositionAt, upperLayer] using
            childTree_positionAt S ep (upperLayer S ⟨layer, by omega⟩)
              (by simp [upperLayer])
        simpa only [hc] using ha.1
      · simpa only [selectLayer, ite_eq_right ha] using hroot

/-- At a selected upper layer, its actual message/certificate pair differs from the reference. -/
theorem selectLayer_not_aligned [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) (layer : ℕ) (hlayer : layer < S.d) :
    let selected := selectLayer hash family pp ends references ep msg sig layer hlayer
    selected.val = 0 ∨ ∃ i : Fin (S.d - 1), selected.val = i.val + 1 ∧
      ¬ UpperAligned hash family pp ends references ep msg sig i := by
  induction layer with
  | zero => exact Or.inl rfl
  | succ layer ih =>
      by_cases ha : UpperAligned hash family pp ends references ep msg sig ⟨layer, by omega⟩
      · simpa only [selectLayer, ite_eq_left ha] using ih (by omega)
      · exact Or.inr ⟨⟨layer, by omega⟩, by simp only [selectLayer, ite_eq_right ha], ha⟩

/-- If the walk reaches the bottom, all upper signature pieces equal their fixed references. -/
theorem selectLayer_zero_references [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) (layer : ℕ) (hlayer : layer < S.d)
    (hzero : (selectLayer hash family pp ends references ep msg sig layer hlayer).val = 0) :
    ∀ i : Fin (S.d - 1), i.val + 1 ≤ layer →
      references (upperPositionAt S ep i) = some (sig.upper i) := by
  induction layer with
  | zero => intro i hi; omega
  | succ layer ih =>
      by_cases ha : UpperAligned hash family pp ends references ep msg sig ⟨layer, by omega⟩
      · have hz : (selectLayer hash family pp ends references ep msg sig layer
            (by omega)).val = 0 := by simpa only [selectLayer, ite_eq_left ha] using hzero
        intro i hi
        by_cases heq : i.val = layer
        · have hiEq : i = ⟨layer, by omega⟩ := Fin.ext heq
          simpa only [hiEq] using ha.2
        · exact ih (by omega) hz i (by omega)
      · simp only [selectLayer, ite_eq_right ha] at hzero
        omega

/-- Read the selected component after the forgery has been observed. -/
@[expose] def selectedCandidate? [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) : Option (ComponentCandidate M R H S) :=
  let selected := selectedLayer hash family pp ends references ep msg sig
  candidateAt? hash family pp ep msg sig selected.val selected.isLt

/-- A valid top-root match supplies a selected component recovering its actual addressed root. -/
theorem selectedCandidate?_binding [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S)
    (hroot : recoverRoot hash family pp ep msg sig =
      some (componentRoot hash pp ends (topTree S))) :
    ∃ candidate, selectedCandidate? hash family pp ends references ep msg sig = some candidate ∧
      recoverComponent hash family pp candidate.position candidate.message candidate.signature =
        some (componentRoot hash pp ends candidate.position.1) := by
  have htop : recoverThrough hash family pp ep msg sig (S.d - 1) (by have := S.d_pos; omega) =
      some (componentRoot hash pp ends
        (positionAt S ep ⟨S.d - 1, by have := S.d_pos; omega⟩).1) := by
    simpa only [recoverRoot, positionAt_topTree] using hroot
  have hs := selectLayer_root hash family pp ends references ep msg sig _ _ htop
  obtain ⟨candidate, hc, hr⟩ := candidateAt?_of_recoverThrough hash family pp ep msg sig
    (selectedLayer hash family pp ends references ep msg sig).val
    (selectedLayer hash family pp ends references ep msg sig).isLt _ hs
  have hp := candidateAt?_position hash family pp ep msg sig _ _ candidate hc
  exact ⟨candidate, hc, hr.trans
    (congrArg (fun p : OTSPosition S => some (componentRoot hash pp ends p.1)) hp.symm)⟩

/-- Actual private upper-reference signatures used by the source forest walk. -/
@[expose] def sourceReferences (hash : HashInstance PP T X H S)
    (out : Security.Result PP H M R Coins S) (p : UpperPosition S) :
    Option (GXMSS.Signature R H S.h S.v) := Security.referenceSignatureAt hash out p.1

/-- The actual source candidate selected after observing the entire global forgery. -/
@[expose] def sourceCandidate? [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) : Option (ComponentCandidate M R H S) :=
  selectedCandidate? hash family out.sk.seed out.sk.endpoints (sourceReferences hash out)
    out.forgery.1 out.forgery.2.1 out.forgery.2.2

/-- The selected source candidate together with its actually accepted re-encoding. -/
@[expose] def sourceDecoded? [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) :
    Option (ComponentCandidate M R H S × Codeword S.v (2 ^ S.w)) := do
  let candidate ← sourceCandidate? hash family out
  let word ← family.value candidate.position out.sk.seed candidate.message
    candidate.signature.randomizer
  pure (candidate, word)

/-- Complete the candidate's revealed chain prefixes at its actual accepted digits. -/
@[expose] def completedLeaf (hash : HashInstance PP T X H S) (pp : PP)
    (candidate : ComponentCandidate M R H S) (word : Codeword S.v (2 ^ S.w)) : Fin S.v → H :=
  fun i => (hash.componentHash candidate.position.1).chain pp candidate.position.2 i
    (word i) (2 ^ S.w - 1 - (word i).val) (candidate.signature.ots i)

/-- Extract a global Merkle collision with the actual honest opening designated first. -/
@[expose] def sourceMerkleWitness? [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) : Option (HashCollision T X) := do
  let (candidate, word) ← sourceDecoded? hash family out
  let p := candidate.position
  (hash.componentHash p.1).findMerkleCollision out.sk.seed p.2 (out.sk.endpoints p)
    (completedLeaf hash out.sk.seed candidate word)
    ((hash.componentHash p.1).authPath out.sk.seed (fun ep => out.sk.endpoints (p.1, ep)) p.2)
    candidate.signature.path

/-- Extract a same-word chain merge using the canonical reference signature as the first path. -/
@[expose] def sourceSameWordWitness? [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) : Option (HashCollision T X) := do
  let (candidate, word) ← sourceDecoded? hash family out
  let reference ← Security.referenceAt hash out candidate.position
  let wr ← reference.result
  if wr.1 = word then
    let p := candidate.position
    let canonical := componentSignature hash out.sk p wr
    let i ← findUnequalCoordinate canonical.ots candidate.signature.ots
    let d ← (hash.componentHash p.1).findChainCollision out.sk.seed p.2 i (wr.1 i)
      (2 ^ S.w - 1 - (wr.1 i).val) (canonical.ots i) (candidate.signature.ots i)
    pure ⟨(hash.componentHash p.1).chainTweak (p.2, i, ⟨(wr.1 i).val + d.val, by
        have := (wr.1 i).isLt; have := d.isLt; omega⟩),
      hash.digestInput ((hash.componentHash p.1).chain out.sk.seed p.2 i (wr.1 i) d
        (canonical.ots i)),
      hash.digestInput ((hash.componentHash p.1).chain out.sk.seed p.2 i (wr.1 i) d
        (candidate.signature.ots i))⟩
  else none

/-- Extract a chain-cut collision after the selected reference word's designated cut. -/
@[expose] def sourceChainCutWitness? [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) : Option (HashCollision T X) := do
  let (candidate, word) ← sourceDecoded? hash family out
  let reference ← Security.referenceAt hash out candidate.position
  let wr ← reference.result
  let p := candidate.position
  let canonical := componentSignature hash out.sk p wr
  let i ← findSmallerCoordinate wr.1 word
  let cut ← (hash.componentHash p.1).findChainCut out.sk.seed p.2 i
    (word i) (wr.1 i) (2 ^ S.w - 1) (canonical.ots i) (candidate.signature.ots i)
  match cut with
  | .inl _ => none
  | .inr d =>
      pure ⟨(hash.componentHash p.1).chainTweak (p.2, i, ⟨(wr.1 i).val + d.val, by
          have := (wr.1 i).isLt; have := d.isLt; omega⟩),
        hash.digestInput ((hash.componentHash p.1).chain out.sk.seed p.2 i (wr.1 i) d
          (canonical.ots i)),
        hash.digestInput ((hash.componentHash p.1).chain out.sk.seed p.2 i (wr.1 i) d
          ((hash.componentHash p.1).chain out.sk.seed p.2 i (word i)
            ((wr.1 i).val - (word i).val) (candidate.signature.ots i)))⟩

/-- An equal-word encoding reference at the same full coordinate with a distinct query pair. -/
@[expose] def sourceEncodingCollision [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) : Bool :=
  match sourceDecoded? hash family out with
  | none => false
  | some (candidate, word) =>
      match Security.referenceAt hash out candidate.position with
      | none => false
      | some reference =>
          match reference.result with
          | none => false
          | some wr => decide (wr.1 = word ∧
              ((⟨reference.position, reference.message⟩ : Security.FamilyEncoding.Query M H S),
                wr.2) ≠
              ((⟨candidate.position, candidate.message⟩ : Security.FamilyEncoding.Query M H S),
                candidate.signature.randomizer))

/-- Native source wins with a returned globally selected Merkle collision. -/
@[expose] noncomputable def sourceMerkleBad [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R)
    (out : Security.Result PP H M R sampling.internal.Coins S) : Bool :=
  Security.sourceStrongObservation hash family sampling out &&
    (sourceMerkleWitness? hash family out).isSome

/-- Native source wins with an actual equal-word, distinct-pair encoding reference. -/
@[expose] noncomputable def sourceEncodingBad [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R)
    (out : Security.Result PP H M R sampling.internal.Coins S) : Bool :=
  Security.sourceStrongObservation hash family sampling out &&
    sourceEncodingCollision hash family out

/-- Native source wins with returned same-word chain collisions, including altered certificates. -/
@[expose] noncomputable def sourceSameWordBad [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R)
    (out : Security.Result PP H M R sampling.internal.Coins S) : Bool :=
  Security.sourceStrongObservation hash family sampling out &&
    (sourceSameWordWitness? hash family out).isSome

/-- Native source wins with returned collisions strictly after a successful reference's cut. -/
@[expose] noncomputable def sourceChainCutBad [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R)
    (out : Security.Result PP H M R sampling.internal.Coins S) : Bool :=
  Security.sourceStrongObservation hash family sampling out &&
    (sourceChainCutWitness? hash family out).isSome

/-- Remaining native source wins after the four actual collision observations are excluded. -/
@[expose] noncomputable def sourceResidual [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R)
    (out : Security.Result PP H M R sampling.internal.Coins S) : Bool :=
  Security.sourceStrongObservation hash family sampling out &&
    !(sourceMerkleBad hash family sampling out || sourceEncodingBad hash family sampling out ||
      sourceSameWordBad hash family sampling out || sourceChainCutBad hash family sampling out)

/-- Every returned source win is covered by the four actual collision flags or the residual. -/
theorem sourceStrong_eq_partition [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (out : Security.Result PP H M R sampling.internal.Coins S) :
    Security.sourceStrongObservation hash family sampling out =
      (sourceMerkleBad hash family sampling out || sourceEncodingBad hash family sampling out ||
        sourceSameWordBad hash family sampling out || sourceChainCutBad hash family sampling out ||
        sourceResidual hash family sampling out) := by
  unfold sourceResidual
  cases hs : Security.sourceStrongObservation hash family sampling out with
  | false => simp [sourceMerkleBad, sourceEncodingBad, sourceSameWordBad, sourceChainCutBad, hs]
  | true =>
      cases sourceMerkleBad hash family sampling out <;>
        cases sourceEncodingBad hash family sampling out <;>
        cases sourceSameWordBad hash family sampling out <;>
        cases sourceChainCutBad hash family sampling out <;> simp

/-- The residual retains source validity and excludes each of the four actual collision flags. -/
theorem sourceResidual_spec [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (out : Security.Result PP H M R sampling.internal.Coins S)
    (h : sourceResidual hash family sampling out = true) :
    Security.sourceStrongObservation hash family sampling out = true ∧
      sourceMerkleBad hash family sampling out = false ∧
      sourceEncodingBad hash family sampling out = false ∧
      sourceSameWordBad hash family sampling out = false ∧
      sourceChainCutBad hash family sampling out = false := by
  simpa [sourceResidual, and_assoc] using h

private theorem boolMap_or_le {A : Type} (oa : ProbComp A) (f g : A → Bool) :
    𝒟[(fun a => f a || g a) <$> oa] {true} ≤
      𝒟[f <$> oa] {true} + 𝒟[g <$> oa] {true} := by
  simp only [map_eq_bind_pure_comp]
  apply OracleComp.evalDist_bind_apply_le_add_of_support oa
    (fun a => pure (f a || g a)) (fun a => pure (f a)) (fun a => pure (g a))
    (by measurability)
  intro a _
  cases f a <;> cases g a <;> simp

private theorem boolMap_partition_le {A : Type} (oa : ProbComp A)
    (strong m e s c r : A → Bool)
    (h : ∀ a, strong a = (m a || e a || s a || c a || r a)) :
    𝒟[strong <$> oa] {true} ≤ 𝒟[m <$> oa] {true} + 𝒟[e <$> oa] {true} +
      𝒟[s <$> oa] {true} + 𝒟[c <$> oa] {true} + 𝒟[r <$> oa] {true} := by
  rw [funext h]
  have hme := boolMap_or_le oa m e
  have hmes := boolMap_or_le oa (fun a => m a || e a) s
  have hmesc := boolMap_or_le oa (fun a => m a || e a || s a) c
  have hmescr := boolMap_or_le oa (fun a => m a || e a || s a || c a) r
  have hmes' := hmes.trans (add_le_add hme (le_refl (𝒟[s <$> oa] {true})))
  have hmesc' := hmesc.trans (add_le_add hmes' (le_refl (𝒟[c <$> oa] {true})))
  exact hmescr.trans (add_le_add hmesc' (le_refl (𝒟[r <$> oa] {true})))

/-- Native successful-output mass of actual source wins is covered without dropping failure mass. -/
theorem sourceStrong_mass_le_partition [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S) :
    Security.sourceStrongOutputMeasure hash family sampling adv {true} ≤
      𝒟[sourceMerkleBad hash family sampling <$>
        Security.sourceProgram hash family sampling adv] {true} +
      𝒟[sourceEncodingBad hash family sampling <$>
        Security.sourceProgram hash family sampling adv] {true} +
      𝒟[sourceSameWordBad hash family sampling <$>
        Security.sourceProgram hash family sampling adv] {true} +
      𝒟[sourceChainCutBad hash family sampling <$>
        Security.sourceProgram hash family sampling adv] {true} +
      𝒟[sourceResidual hash family sampling <$>
        Security.sourceProgram hash family sampling adv] {true} := by
  unfold Security.sourceStrongOutputMeasure
  exact boolMap_partition_le (Security.sourceProgram hash family sampling adv)
    (Security.sourceStrongObservation hash family sampling)
    (sourceMerkleBad hash family sampling) (sourceEncodingBad hash family sampling)
    (sourceSameWordBad hash family sampling) (sourceChainCutBad hash family sampling)
    (sourceResidual hash family sampling) (sourceStrong_eq_partition hash family sampling)

/-- Decoding a selected source component records its exact accepted value equation. -/
theorem sourceDecoded?_spec [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) (candidate : ComponentCandidate M R H S)
    (word : Codeword S.v (2 ^ S.w))
    (h : sourceDecoded? hash family out = some (candidate, word)) :
    sourceCandidate? hash family out = some candidate ∧
      family.value candidate.position out.sk.seed candidate.message candidate.signature.randomizer =
        some word := by
  obtain ⟨actual, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨actualWord, hw, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  exact ⟨ha, hw⟩

/-- Returned Merkle collisions are sound and their honest inputs are globally registered. -/
theorem sourceMerkleWitness?_spec [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) (collision : HashCollision T X)
    (hc : sourceMerkleWitness? hash family out = some collision) :
    collision.Sound hash.thf out.sk.seed ∧
      (collision.tweak, collision.first) ∈
        setupLedger hash out.sk.seed out.sk.starts out.sk.endpoints := by
  obtain ⟨⟨candidate, word⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  have hs := (hash.componentHash candidate.position.1).findMerkleCollision_sound out.sk.seed
    candidate.position.2 (out.sk.endpoints candidate.position)
    (completedLeaf hash out.sk.seed candidate word)
    ((hash.componentHash candidate.position.1).authPath out.sk.seed
      (fun ep => out.sk.endpoints (candidate.position.1, ep)) candidate.position.2)
    candidate.signature.path hc
  have hm := ((hash.componentHash candidate.position.1).findMerkleCollision_mem_queries
    out.sk.seed candidate.position.2 (out.sk.endpoints candidate.position)
    (completedLeaf hash out.sk.seed candidate word)
    ((hash.componentHash candidate.position.1).authPath out.sk.seed
      (fun ep => out.sk.endpoints (candidate.position.1, ep)) candidate.position.2)
    candidate.signature.path hc).1
  exact ⟨by simpa only [HashInstance.componentHash_thf] using hs,
    merkleOpeningTarget_mem_setupLedger hash out.sk.seed out.sk.starts out.sk.endpoints
      candidate.position.1 candidate.position.2 _ hm⟩

/-- Returned same-word witnesses retain the ordinary honest trajectory in the global ledger. -/
theorem sourceSameWordWitness?_spec [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) (collision : HashCollision T X)
    (hc : sourceSameWordWitness? hash family out = some collision) :
    collision.Sound hash.thf out.sk.seed ∧
      (collision.tweak, collision.first) ∈ chainLedger hash out.sk.seed out.sk.starts := by
  obtain ⟨⟨candidate, word⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨reference, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨wr, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  split_ifs at hc with heq
  · obtain ⟨i, _, hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨d, hd, hc⟩ := Option.bind_eq_some_iff.mp hc
    cases Option.some.inj hc
    have hs := (hash.componentHash candidate.position.1).findChainCollision_hash_sound
      out.sk.seed candidate.position.2 i (wr.1 i) (2 ^ S.w - 1 - (wr.1 i).val)
      ((componentSignature hash out.sk candidate.position wr).ots i)
      (candidate.signature.ots i) (by have := (wr.1 i).isLt; omega) hd
    refine ⟨by simpa only [HashInstance.componentHash_thf,
      HashInstance.componentHash_digestInput] using hs, ?_⟩
    have hm := chainTarget_mem_chainLedger hash out.sk.seed out.sk.starts candidate.position.1
      candidate.position.2 i ⟨(wr.1 i).val + d.val, by
        have := (wr.1 i).isLt; have := d.isLt; omega⟩
    simpa only [componentSignature, GXMSS.signatureOfWord, componentSecretKey,
      GXMSS.HashInstance.chain_add, Nat.zero_add] using hm
/-- Returned cut collisions retain the honest post-cut input at an actual global chain target. -/
theorem sourceChainCutWitness?_spec [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (out : Security.Result PP H M R Coins S) (collision : HashCollision T X)
    (hc : sourceChainCutWitness? hash family out = some collision) :
    collision.Sound hash.thf out.sk.seed ∧
      (collision.tweak, collision.first) ∈ chainLedger hash out.sk.seed out.sk.starts := by
  obtain ⟨⟨candidate, word⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨reference, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨wr, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  obtain ⟨i, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨cut, hcut, hc⟩ := Option.bind_eq_some_iff.mp hc
  cases cut with
  | inl _ => cases hc
  | inr d =>
      cases Option.some.inj hc
      have hs := (hash.componentHash candidate.position.1).findChainCut_hash_sound out.sk.seed
        candidate.position.2 i (word i) (wr.1 i) (2 ^ S.w - 1)
        ((componentSignature hash out.sk candidate.position wr).ots i) (candidate.signature.ots i)
        (by have := (wr.1 i).isLt; omega) le_rfl hcut
      refine ⟨by simpa only [HashInstance.componentHash_thf,
        HashInstance.componentHash_digestInput] using hs, ?_⟩
      have hm := chainTarget_mem_chainLedger hash out.sk.seed out.sk.starts candidate.position.1
        candidate.position.2 i ⟨(wr.1 i).val + d.val, by
          have := (wr.1 i).isLt; have := d.isLt; omega⟩
      simpa only [componentSignature, GXMSS.signatureOfWord, componentSecretKey,
        GXMSS.HashInstance.chain_add, Nat.zero_add] using hm

/-- Actual key generation and native source execution retain a consistent full forest key pair. -/
theorem sourceProgram_consistent [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (out : Security.Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv)) :
    Consistent hash out.pk out.sk := by
  classical
  simp only [Security.sourceProgram, keygen, bind_assoc, pure_bind,
    mem_support_bind_iff] at hout
  obtain ⟨pp, _, starts, _, coins, _, hout⟩ := hout
  obtain ⟨hpk, hsk, _⟩ := Security.runWithKeys_support_keys hash family sampling adv
    (keys hash pp starts coins).1 (keys hash pp starts coins).2 out hout
  rw [hpk, hsk]
  exact consistent_keys hash pp starts coins

/-- A native source win has a selected component bound to its actual addressed forest root. -/
theorem sourceCandidate?_binding [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (out : Security.Result PP H M R sampling.internal.Coins S)
    (hc : Consistent hash out.pk out.sk)
    (hstrong : Security.sourceStrongObservation hash family sampling out = true) :
    ∃ candidate, sourceCandidate? hash family out = some candidate ∧
      recoverComponent hash family out.sk.seed candidate.position candidate.message
        candidate.signature = some (componentRoot hash out.sk.seed out.sk.endpoints
          candidate.position.1) := by
  have hv := hstrong
  simp only [Security.sourceStrongObservation, Security.sourceObservation,
    SyncSignatureUnforgeability.strongValid, scheme, Bool.and_eq_true] at hv
  have hr := of_decide_eq_true hv.1
  rcases hc with ⟨hseed, _, hpkroot⟩
  apply selectedCandidate?_binding hash family out.sk.seed out.sk.endpoints
    (sourceReferences hash out) out.forgery.1 out.forgery.2.1 out.forgery.2.2
  simpa only [hseed, hpkroot] using hr

/-- Source validity provides the exact successful selected re-encoding and completed root. -/
theorem sourceDecoded?_binding [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (out : Security.Result PP H M R sampling.internal.Coins S)
    (hc : Consistent hash out.pk out.sk)
    (hstrong : Security.sourceStrongObservation hash family sampling out = true) :
    ∃ candidate word, sourceDecoded? hash family out = some (candidate, word) ∧
      family.value candidate.position out.sk.seed candidate.message
        candidate.signature.randomizer = some word ∧
      (hash.componentHash candidate.position.1).recoverRoot out.sk.seed candidate.position.2
        (completedLeaf hash out.sk.seed candidate word) candidate.signature.path =
          componentRoot hash out.sk.seed out.sk.endpoints candidate.position.1 := by
  obtain ⟨candidate, hcandidate, hr⟩ := sourceCandidate?_binding hash family sampling out hc hstrong
  obtain ⟨word, hword, hr⟩ := word_of_recoverComponent hash family out.sk.seed candidate _ hr
  refine ⟨candidate, word, ?_, hword, hr⟩
  simp [sourceDecoded?, hcandidate, hword]

/-- Residual source wins have equal complete openings and per-chain endpoint equality at their
post-forgery selected component, without a component guess or a maximum-digit premise. -/
theorem sourceResidual_opening [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (out : Security.Result PP H M R sampling.internal.Coins S)
    (hc : Consistent hash out.pk out.sk)
    (hres : sourceResidual hash family sampling out = true) :
    ∃ candidate word, sourceDecoded? hash family out = some (candidate, word) ∧
      family.value candidate.position out.sk.seed candidate.message
        candidate.signature.randomizer = some word ∧
      (out.sk.endpoints candidate.position,
        (hash.componentHash candidate.position.1).authPath out.sk.seed
          (fun ep => out.sk.endpoints (candidate.position.1, ep)) candidate.position.2) =
        (completedLeaf hash out.sk.seed candidate word, candidate.signature.path) := by
  obtain ⟨hstrong, hbad, _, _, _⟩ := sourceResidual_spec hash family sampling out hres
  obtain ⟨candidate, word, hd, hw, hr⟩ := sourceDecoded?_binding hash family sampling out hc hstrong
  refine ⟨candidate, word, hd, hw, ?_⟩
  by_contra hne
  have hs := (hash.componentHash candidate.position.1).findMerkleCollision_isSome_of_honest
    out.sk.seed (fun ep => out.sk.endpoints (candidate.position.1, ep)) candidate.position.2
    (completedLeaf hash out.sk.seed candidate word) candidate.signature.path hne hr
  have hwitness : (sourceMerkleWitness? hash family out).isSome = true := by
    simpa only [sourceMerkleWitness?, hd, Option.bind_eq_bind, Option.bind_some] using hs
  have hfalse : (sourceMerkleWitness? hash family out).isSome = false := by
    simpa only [sourceMerkleBad, hstrong, Bool.true_and] using hbad
  exact Bool.false_ne_true (hfalse.symm.trans hwitness)

/-- Canonical revealed prefixes complete to the stored endpoints of a consistent key. -/
theorem componentSignature_chain_complete (hash : HashInstance PP T X H S)
    (sk : SecretKey PP H Coins S) (hend : sk.endpoints = endpoints hash sk.seed sk.starts)
    (p : OTSPosition S) (wr : Codeword S.v (2 ^ S.w) × R) :
    (fun i => (hash.componentHash p.1).chain sk.seed p.2 i (wr.1 i)
      (2 ^ S.w - 1 - (wr.1 i).val) ((componentSignature hash sk p wr).ots i)) =
        sk.endpoints p := by
  funext i
  change (hash.componentHash p.1).chain sk.seed p.2 i (wr.1 i)
    (2 ^ S.w - 1 - (wr.1 i).val)
    ((hash.componentHash p.1).chain sk.seed p.2 i 0 (wr.1 i) (sk.starts p i)) = _
  rw [GXMSS.HashInstance.chain_complete_digit, hend]
  rfl

/-- In the residual, a successful reference with the forged word has exactly the forged OTS data.
Otherwise the actual same-word merge finder would have returned a removed global collision. -/
theorem sourceResidual_sameWord_ots [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (out : Security.Result PP H M R sampling.internal.Coins S)
    (hc : Consistent hash out.pk out.sk) (hres : sourceResidual hash family sampling out = true)
    (candidate : ComponentCandidate M R H S) (word : Codeword S.v (2 ^ S.w))
    (hd : sourceDecoded? hash family out = some (candidate, word))
    (hopening : (out.sk.endpoints candidate.position,
        (hash.componentHash candidate.position.1).authPath out.sk.seed
          (fun ep => out.sk.endpoints (candidate.position.1, ep)) candidate.position.2) =
      (completedLeaf hash out.sk.seed candidate word, candidate.signature.path))
    (reference : Security.FamilyEncoding.Record M H R S)
    (href : Security.referenceAt hash out candidate.position = some reference)
    (wr : Codeword S.v (2 ^ S.w) × R) (hresult : reference.result = some wr)
    (heq : wr.1 = word) :
    (componentSignature hash out.sk candidate.position wr).ots = candidate.signature.ots := by
  subst word
  by_contra hne
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (findUnequalCoordinate_isSome
    (componentSignature hash out.sk candidate.position wr).ots candidate.signature.ots hne)
  have hiNe := findUnequalCoordinate_sound _ _ hi
  have hcanonical := congrFun
    (componentSignature_chain_complete hash out.sk hc.2.1 candidate.position wr) i
  have hforged := congrFun (congrArg Prod.fst hopening) i
  have hends : (hash.componentHash candidate.position.1).chain out.sk.seed candidate.position.2 i
      (wr.1 i) (2 ^ S.w - 1 - (wr.1 i).val)
      ((componentSignature hash out.sk candidate.position wr).ots i) =
    (hash.componentHash candidate.position.1).chain out.sk.seed candidate.position.2 i
      (wr.1 i) (2 ^ S.w - 1 - (wr.1 i).val) (candidate.signature.ots i) := by
    simpa only [completedLeaf] using hcanonical.trans hforged
  obtain ⟨d, hmerge⟩ := Option.isSome_iff_exists.mp
    ((hash.componentHash candidate.position.1).findChainCollision_isSome out.sk.seed
      candidate.position.2 i (wr.1 i) (2 ^ S.w - 1 - (wr.1 i).val)
      ((componentSignature hash out.sk candidate.position wr).ots i)
      (candidate.signature.ots i) hiNe hends)
  have hwitness : (sourceSameWordWitness? hash family out).isSome = true := by
    simp [sourceSameWordWitness?, hd, href, hresult, hi, hmerge]
  obtain ⟨hstrong, _, _, hbad, _⟩ := sourceResidual_spec hash family sampling out hres
  have hfalse : (sourceSameWordWitness? hash family out).isSome = false := by
    simpa only [sourceSameWordBad, hstrong, Bool.true_and] using hbad
  exact Bool.false_ne_true (hfalse.symm.trans hwitness)

/-- Interpreting a digest in an upper message fibre preserves its value injectively. -/
theorem internalMessage_injective (p : UpperPosition S) :
    Function.Injective (internalMessage (M := M) (H := H) p) := by
  intro x y h
  simpa [internalMessage, Message, p.property] using h

/-- Equality of the two stored signature components is equality of the complete forest signature. -/
theorem fullSignature_ext (left right : Signature R H S)
    (hbottom : left.bottom = right.bottom) (hupper : left.upper = right.upper) : left = right := by
  cases left
  cases right
  cases hbottom
  cases hupper
  rfl

/-- An actual source win excludes exactly its previously returned full message/signature pair. -/
theorem sourceStrong_pair_fresh [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (out : Security.Result PP H M R sampling.internal.Coins S)
    (hstrong : Security.sourceStrongObservation hash family sampling out = true) :
    out.history out.forgery.1 ≠ some (out.forgery.2.1, some out.forgery.2.2) := by
  simp only [Security.sourceStrongObservation, Security.sourceObservation,
    SyncSignatureUnforgeability.strongValid, SyncSignatureUnforgeability.strongFresh,
    Bool.and_eq_true] at hstrong
  exact of_decide_eq_true hstrong.2

/-- Every private upper reference of an actual source result is its fixed optional certificate. -/
theorem sourceReferences_eq_certificate [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (out : Security.Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv)) (p : UpperPosition S) :
    sourceReferences hash out p = certificate hash family sampling.internal out.sk p := by
  classical
  have hu := Security.sourceProgram_upperResults hash family sampling adv out hout
  simp [sourceReferences, Security.referenceSignatureAt, Security.referenceAt, p.property,
    hu, Security.upperResults, certificate]

/-- Strong global pair freshness induces pair freshness at the post-forgery selected component.
The bottom case uses the native first-attempt/history association, including full-signing failure;
the upper case uses the complete fixed private reference, whether disclosed or not. -/
theorem sourceCandidate_pair_fresh [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (out : Security.Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv))
    (hstrong : Security.sourceStrongObservation hash family sampling out = true)
    (candidate : ComponentCandidate M R H S)
    (hcan : sourceCandidate? hash family out = some candidate)
    (reference : Security.FamilyEncoding.Record M H R S)
    (href : Security.referenceAt hash out candidate.position = some reference)
    (wr : Codeword S.v (2 ^ S.w) × R) (hresult : reference.result = some wr) :
    ((⟨reference.position, reference.message⟩ : Security.FamilyEncoding.Query M H S),
        componentSignature hash out.sk candidate.position wr) ≠
      ((⟨candidate.position, candidate.message⟩ : Security.FamilyEncoding.Query M H S),
        candidate.signature) := by
  intro hmatch
  let selected := selectedLayer hash family out.sk.seed out.sk.endpoints (sourceReferences hash out)
    out.forgery.1 out.forgery.2.1 out.forgery.2.2
  change candidateAt? hash family out.sk.seed out.forgery.1 out.forgery.2.1 out.forgery.2.2
    selected.val selected.isLt = some candidate at hcan
  have hcases := selectLayer_not_aligned hash family out.sk.seed out.sk.endpoints
    (sourceReferences hash out) out.forgery.1 out.forgery.2.1 out.forgery.2.2 (S.d - 1)
    (by have := S.d_pos; omega)
  change selected.val = 0 ∨ ∃ i : Fin (S.d - 1), selected.val = i.val + 1 ∧
    ¬ UpperAligned hash family out.sk.seed out.sk.endpoints (sourceReferences hash out)
      out.forgery.1 out.forgery.2.1 out.forgery.2.2 i at hcases
  rcases hcases with hz | ⟨i, hi, hnot⟩
  · have heq : candidate = ⟨bottomPosition S out.forgery.1,
        bottomMessage out.forgery.1 out.forgery.2.1, out.forgery.2.2.bottom⟩ := by
      have hposition : selected = ⟨0, S.d_pos⟩ := Fin.ext hz
      have hread := congrArg (fun l : Fin S.d => candidateAt? hash family out.sk.seed
        out.forgery.1 out.forgery.2.1 out.forgery.2.2 l.val l.isLt) hposition
      exact (Option.some.inj (hread.symm.trans hcan)).symm
    subst candidate
    have hupper : ∀ i, certificate hash family sampling.internal out.sk
        (upperPositionAt S out.forgery.1 i) = some (out.forgery.2.2.upper i) := by
      intro i
      rw [← sourceReferences_eq_certificate hash family sampling adv out hout]
      exact selectLayer_zero_references hash family out.sk.seed out.sk.endpoints
        (sourceReferences hash out) out.forgery.1 out.forgery.2.1 out.forgery.2.2
        (S.d - 1) (by have := S.d_pos; omega) hz i (by have := i.isLt; omega)
    have hh := Security.history_of_referenceAt_bottom_success hash family sampling adv out hout
      out.forgery.1 out.forgery.2.1 reference wr out.forgery.2.2.upper href hresult
      (congrArg Prod.fst hmatch) hupper
    have hs : (⟨componentSignature hash out.sk (bottomPosition S out.forgery.1) wr,
        out.forgery.2.2.upper⟩ : Signature R H S) = out.forgery.2.2 :=
      fullSignature_ext _ _ (congrArg Prod.snd hmatch) rfl
    rw [hs] at hh
    exact sourceStrong_pair_fresh hash family sampling out hstrong hh
  · have hposition : selected = ⟨i.val + 1, by have := i.isLt; omega⟩ := Fin.ext hi
    have hread := congrArg (fun l : Fin S.d => candidateAt? hash family out.sk.seed
      out.forgery.1 out.forgery.2.1 out.forgery.2.2 l.val l.isLt) hposition
    have hcan' := hread.symm.trans hcan
    obtain ⟨child, hchild, hcan⟩ := Option.bind_eq_some_iff.mp hcan'
    cases Option.some.inj hcan
    let p := upperPositionAt S out.forgery.1 i
    have hentry : reference = ⟨p.1, internalMessage p
        (componentRoot hash out.sk.seed out.sk.endpoints (childTree S p)),
        (out.upperResults p).output⟩ := by
      simpa [Security.referenceAt, p, upperPositionAt, upperLayer] using href.symm
    subst reference
    have hquery := congrArg Prod.fst hmatch
    have hmessage : internalMessage (M := M) p
        (componentRoot hash out.sk.seed out.sk.endpoints (childTree S p)) =
        internalMessage (M := M) p child := eq_of_heq (Sigma.mk.inj_iff.mp hquery).2
    have hchildEq := internalMessage_injective (M := M) p hmessage
    have hsig : componentSignature hash out.sk p.1 wr = out.forgery.2.2.upper i :=
      congrArg Prod.snd hmatch
    change Security.referenceAt hash out p.1 = some
      ⟨p.1, internalMessage p
        (componentRoot hash out.sk.seed out.sk.endpoints (childTree S p)),
        (out.upperResults p).output⟩ at href
    change (out.upperResults p).output = some wr at hresult
    have hreference : sourceReferences hash out p = some (out.forgery.2.2.upper i) := by
      change (Security.referenceAt hash out p.1).bind
        (fun entry => entry.result.map (componentSignature hash out.sk p.1)) = _
      rw [href]
      simp only [Option.bind_some]
      rw [hresult]
      exact congrArg some hsig
    exact hnot ⟨hchild.trans (congrArg some hchildEq.symm), hreference⟩

/-- A component signature is determined by its randomizer, chain prefixes and leaf-first path. -/
theorem componentSignature_ext (left right : GXMSS.Signature R H S.h S.v)
    (hrandomizer : left.randomizer = right.randomizer) (hots : left.ots = right.ots)
    (hpath : left.path = right.path) : left = right := by
  cases left
  cases right
  cases hrandomizer
  cases hots
  cases hpath
  rfl

/-- In the residual, every successful private reference has a word distinct from the forged word.
Same-word altered signatures are removed by the collision finder; identical component pairs
contradict the actual global strong-pair freshness at the selected layer. -/
theorem sourceResidual_reference_word_ne [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (out : Security.Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv))
    (hres : sourceResidual hash family sampling out = true)
    (candidate : ComponentCandidate M R H S) (word : Codeword S.v (2 ^ S.w))
    (hd : sourceDecoded? hash family out = some (candidate, word))
    (hopening : (out.sk.endpoints candidate.position,
        (hash.componentHash candidate.position.1).authPath out.sk.seed
          (fun ep => out.sk.endpoints (candidate.position.1, ep)) candidate.position.2) =
      (completedLeaf hash out.sk.seed candidate word, candidate.signature.path))
    (reference : Security.FamilyEncoding.Record M H R S)
    (href : Security.referenceAt hash out candidate.position = some reference)
    (wr : Codeword S.v (2 ^ S.w) × R) (hresult : reference.result = some wr) : wr.1 ≠ word := by
  intro heq
  have hc := sourceProgram_consistent hash family sampling adv out hout
  have hots := sourceResidual_sameWord_ots hash family sampling out hc hres candidate word hd
    hopening reference href wr hresult heq
  obtain ⟨hstrong, _, hencoding, _, _⟩ := sourceResidual_spec hash family sampling out hres
  have hpairs :
      ((⟨reference.position, reference.message⟩ : Security.FamilyEncoding.Query M H S), wr.2) =
      ((⟨candidate.position, candidate.message⟩ : Security.FamilyEncoding.Query M H S),
        candidate.signature.randomizer) := by
    by_contra hne
    have ht : sourceEncodingCollision hash family out = true := by
      simp [sourceEncodingCollision, hd, href, hresult, heq, hne]
    have ht' : sourceEncodingBad hash family sampling out = true := by
      simp only [sourceEncodingBad, hstrong, ht, Bool.true_and]
    exact Bool.false_ne_true (hencoding.symm.trans ht')
  have hs : componentSignature hash out.sk candidate.position wr = candidate.signature :=
    componentSignature_ext _ _ (congrArg Prod.snd hpairs) hots (congrArg Prod.snd hopening)
  have hquery := congrArg Prod.fst hpairs
  exact sourceCandidate_pair_fresh hash family sampling adv out hout hstrong candidate
    (sourceDecoded?_spec hash family out candidate word hd).1 reference href wr hresult
    (Prod.ext hquery hs)

/-- The preimage branch of the existing cut finder certifies the full forged reach equation. -/
theorem chainCut_preimage_reaches [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H S.h S.w S.v) (pp : PP)
    (ep : Fin S.branching) (i : Fin S.v) (t s b : ℕ) (x y u : H)
    (h : hash.findChainCut pp ep i t s b x y = some (.inl u)) :
    hash.chain pp ep i t (s - t) y = x := by
  unfold GXMSS.HashInstance.findChainCut at h
  split_ifs at h with heq
  · exact heq
  · simp at h

/-- A residual successful private reference deterministically chooses a smaller forged digit and
the preimage branch of the actual cut finder. The reference may have failed full signing. -/
theorem sourceResidual_reference_cut [SampleableType H] [DecidableEq H] [DecidableEq M]
    [DecidableEq R] [DecidableEq (GXMSS.Signature R H S.h S.v)]
    [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (out : Security.Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv))
    (hres : sourceResidual hash family sampling out = true)
    (candidate : ComponentCandidate M R H S) (word : Codeword S.v (2 ^ S.w))
    (hd : sourceDecoded? hash family out = some (candidate, word))
    (hopening : (out.sk.endpoints candidate.position,
        (hash.componentHash candidate.position.1).authPath out.sk.seed
          (fun ep => out.sk.endpoints (candidate.position.1, ep)) candidate.position.2) =
      (completedLeaf hash out.sk.seed candidate word, candidate.signature.path))
    (reference : Security.FamilyEncoding.Record M H R S)
    (href : Security.referenceAt hash out candidate.position = some reference)
    (wr : Codeword S.v (2 ^ S.w) × R) (hresult : reference.result = some wr) :
    ∃ i u, findSmallerCoordinate wr.1 word = some i ∧ (word i).val < (wr.1 i).val ∧
      (hash.componentHash candidate.position.1).findChainCut out.sk.seed candidate.position.2 i
        (word i) (wr.1 i) (2 ^ S.w - 1)
        ((componentSignature hash out.sk candidate.position wr).ots i)
        (candidate.signature.ots i) = some (.inl u) ∧
      (hash.componentHash candidate.position.1).chain out.sk.seed candidate.position.2 i
        (word i) ((wr.1 i).val - (word i).val) (candidate.signature.ots i) =
          (componentSignature hash out.sk candidate.position wr).ots i := by
  have hc := sourceProgram_consistent hash family sampling adv out hout
  have hne := sourceResidual_reference_word_ne hash family sampling adv out hout hres
    candidate word hd hopening reference href wr hresult
  have hw := (sourceDecoded?_spec hash family out candidate word hd).2
  have hwr := Security.referenceAt_value_eq_some hash family sampling adv out hout
    candidate.position reference href wr.1 wr.2 hresult
  have hrmem := family.mem_code_of_value_eq_some reference.position out.sk.seed reference.message
    wr.2 hwr
  have hp := Security.referenceAt_position hash out candidate.position reference href
  rw [hp] at hrmem
  have hwm := family.mem_code_of_value_eq_some candidate.position out.sk.seed candidate.message
    candidate.signature.randomizer hw
  have hsmaller : (findSmallerCoordinate wr.1 word).isSome :=
    findCoordinate_isSome _ ((family.component candidate.position).incomparable hrmem hwm hne).2
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsmaller
  have hlt := findSmallerCoordinate_sound wr.1 word hi
  have hcanonical := congrFun
    (componentSignature_chain_complete hash out.sk hc.2.1 candidate.position wr) i
  have hforged := congrFun (congrArg Prod.fst hopening) i
  have hends : (hash.componentHash candidate.position.1).chain out.sk.seed candidate.position.2 i
      (wr.1 i) (2 ^ S.w - 1 - (wr.1 i).val)
      ((componentSignature hash out.sk candidate.position wr).ots i) =
    (hash.componentHash candidate.position.1).chain out.sk.seed candidate.position.2 i
      (word i) (2 ^ S.w - 1 - (word i).val) (candidate.signature.ots i) := by
    exact hcanonical.trans hforged
  obtain ⟨cut, hcut⟩ := Option.isSome_iff_exists.mp
    ((hash.componentHash candidate.position.1).findChainCut_isSome_at_max out.sk.seed
      candidate.position.2 i (word i) (wr.1 i)
      ((componentSignature hash out.sk candidate.position wr).ots i) (candidate.signature.ots i)
      hlt (by have := (wr.1 i).isLt; omega) hends)
  cases cut with
  | inl u =>
      exact ⟨i, u, hi, hlt, hcut, chainCut_preimage_reaches _ _ _ _ _ _ _ _ _ _ hcut⟩
  | inr d =>
      have hwitness : (sourceChainCutWitness? hash family out).isSome = true := by
        simp [sourceChainCutWitness?, hd, href, hresult, hi, hcut]
      obtain ⟨hstrong, _, _, _, hbad⟩ := sourceResidual_spec hash family sampling out hres
      have hfalse : (sourceChainCutWitness? hash family out).isSome = false := by
        simpa only [sourceChainCutBad, hstrong, Bool.true_and] using hbad
      exact (Bool.false_ne_true (hfalse.symm.trans hwitness)).elim

/-- A fibrewise non-maximum accepted word deterministically names a final cut reached by the
forged trajectory. This branch requires no successful reference or private prefix material. -/
theorem completedLeaf_final_cut
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (hnonmax : family.NoMaximumOutput) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) (candidate : ComponentCandidate M R H S)
    (word : Codeword S.v (2 ^ S.w))
    (hword : family.value candidate.position pp candidate.message
      candidate.signature.randomizer = some word)
    (hleaf : ends candidate.position = completedLeaf hash pp candidate word) :
    ∃ i, GXMSS.Reductions.findNonMaximumCoordinate word = some i ∧
      (word i).val < 2 ^ S.w - 1 ∧
      (hash.componentHash candidate.position.1).chain pp candidate.position.2 i
        (word i) (2 ^ S.w - 1 - (word i).val) (candidate.signature.ots i) =
          ends candidate.position i := by
  have hn : GXMSS.Reductions.NoMaximumOutput
      (family.atEpoch candidate.position (Fin S.branching)) := by
    intro pp msg r ep actual hactual
    exact hnonmax candidate.position pp msg r actual (by simpa using hactual)
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
    (GXMSS.Reductions.findNonMaximumCoordinate_isSome
      (family.atEpoch candidate.position (Fin S.branching)) hn pp candidate.message
      candidate.signature.randomizer candidate.position.2 word (by simpa using hword))
  exact ⟨i, hi, GXMSS.Reductions.findNonMaximumCoordinate_sound word hi,
    (congrFun hleaf i).symm⟩

end GXMSS.Hypertree.Unforgeability
