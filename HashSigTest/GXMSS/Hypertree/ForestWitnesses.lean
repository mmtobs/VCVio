/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Reductions.ChainCutCollision
meta import HashSigTest.GXMSS.TrustAuditSupport

/-!
# Forest witness and global collision consumers

These controls cover failed private certificates, altered upper OTS data, path-only alterations
and message changes in the top-down walk. Ordinary consumers also check the actual native
collision bounds, raw-bottom-attempt freshness bridge and residual cut endpoints.
-/

public section

namespace GXMSS.Hypertree.ForestWitnessesProbe

open GXMSS.Hypertree.Unforgeability

variable {PP T X H M R : Type} {S : Shape}

/-- A failed upper reference stops the walk even if its fixed result was never disclosed. -/
theorem exhausted_private_reference_stops [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H) (ep : Epoch S) (msg : M) (sig : Signature R H S)
    (layer : ℕ) (hlayer : layer + 1 < S.d) :
    selectLayer hash family pp ends (fun _ => none) ep msg sig (layer + 1) hlayer =
      ⟨layer + 1, hlayer⟩ := by
  simp [selectLayer, UpperAligned]

/-- A differing complete upper signature stops descent, even with an unchanged message. -/
theorem altered_private_reference_stops [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) (i : Fin (S.d - 1))
    (hdifferent : references (upperPositionAt S ep i) ≠ some (sig.upper i)) :
    selectLayer hash family pp ends references ep msg sig (i.val + 1)
      (by have := i.isLt; omega) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  have hnot : ¬ UpperAligned hash family pp ends references ep msg sig i :=
    fun h => hdifferent h.2
  simp only [selectLayer, ite_eq_right hnot]

/-- Changed OTS prefixes at the same upper message are not discarded by the selector. -/
theorem changed_upper_ots_stops [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) (i : Fin (S.d - 1))
    (reference : GXMSS.Signature R H S.h S.v)
    (href : references (upperPositionAt S ep i) = some reference)
    (hne : reference.ots ≠ (sig.upper i).ots) :
    selectLayer hash family pp ends references ep msg sig (i.val + 1)
      (by have := i.isLt; omega) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  apply altered_private_reference_stops hash family pp ends references ep msg sig i
  intro heq
  exact hne (congrArg GXMSS.Signature.ots (Option.some.inj (href.symm.trans heq)))

/-- A path-only alteration also stops the complete-signature comparison. -/
theorem changed_upper_path_stops [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) (i : Fin (S.d - 1))
    (reference : GXMSS.Signature R H S.h S.v)
    (href : references (upperPositionAt S ep i) = some reference)
    (hne : reference.path ≠ (sig.upper i).path) :
    selectLayer hash family pp ends references ep msg sig (i.val + 1)
      (by have := i.isLt; omega) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  apply altered_private_reference_stops hash family pp ends references ep msg sig i
  intro heq
  exact hne (congrArg GXMSS.Signature.path (Option.some.inj (href.symm.trans heq)))

/-- Matching certificate bytes do not conceal a changed recovered child message. -/
theorem changed_child_message_stops [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S) (pp : PP)
    (ends : OTSPosition S → Fin S.v → H)
    (references : UpperPosition S → Option (GXMSS.Signature R H S.h S.v))
    (ep : Epoch S) (msg : M) (sig : Signature R H S) (i : Fin (S.d - 1))
    (hne : recoverThrough hash family pp ep msg sig i.val (by have := i.isLt; omega) ≠
      some (componentRoot hash pp ends (childTree S (upperPositionAt S ep i)))) :
    selectLayer hash family pp ends references ep msg sig (i.val + 1)
      (by have := i.isLt; omega) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  have hnot : ¬ UpperAligned hash family pp ends references ep msg sig i := fun h => hne h.1
  simp only [selectLayer, ite_eq_right hnot]

example := @sourceStrong_mass_le_partition
example := @sourceCandidate_pair_fresh
example := @sourceResidual_opening
example := @sourceResidual_reference_word_ne
example := @sourceResidual_reference_cut
example := @completedLeaf_final_cut
example := @sourceMerkleBad_le_targetCollision
example := @sourceSameWordBad_le_targetCollision
example := @sourceChainCutBad_le_targetCollision

run_cmd Lean.Elab.Command.liftCoreM <|
  GXMSS.Test.TrustAudit.assertStandardAxioms #[
    ``exhausted_private_reference_stops, ``altered_private_reference_stops,
    ``changed_upper_ots_stops, ``changed_upper_path_stops, ``changed_child_message_stops]

run_cmd Lean.Elab.Command.liftTermElabM do
  let modules := #[`HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses,
    `HashSig.GXMSS.Security.Hypertree.Reductions.MerkleCollision,
    `HashSig.GXMSS.Security.Hypertree.Reductions.SameMessageChainCollision,
    `HashSig.GXMSS.Security.Hypertree.Reductions.ChainCutCollision]
  let endpoints := #[(``sourceCandidate_pair_fresh,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses),
    (``sourceStrong_mass_le_partition, `HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses),
    (``sourceResidual_reference_cut, `HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses),
    (``sourceMerkleBad_le_targetCollision,
      `HashSig.GXMSS.Security.Hypertree.Reductions.MerkleCollision),
    (``sourceSameWordBad_le_targetCollision,
      `HashSig.GXMSS.Security.Hypertree.Reductions.SameMessageChainCollision),
    (``sourceChainCutBad_le_targetCollision,
      `HashSig.GXMSS.Security.Hypertree.Reductions.ChainCutCollision)]
  let definitions := #[(``selectedLayer,
      `HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses),
    (``merkleTargetCollisionReduction,
      `HashSig.GXMSS.Security.Hypertree.Reductions.MerkleCollision),
    (``sameMessageChainTargetCollisionReduction,
      `HashSig.GXMSS.Security.Hypertree.Reductions.SameMessageChainCollision),
    (``chainCutTargetCollisionReduction,
      `HashSig.GXMSS.Security.Hypertree.Reductions.ChainCutCollision)]
  GXMSS.Test.TrustAudit.check modules endpoints #[] definitions

end GXMSS.Hypertree.ForestWitnessesProbe
