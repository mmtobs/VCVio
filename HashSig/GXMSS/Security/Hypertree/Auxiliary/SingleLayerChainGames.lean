/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
public import HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all HashSig.GXMSS.Hypertree.SingleLayer
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainMass
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ChainContinuation
import all HashSig.GXMSS.Security.Auxiliary.ChainSplicing
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses
import all HashSig.GXMSS.Security.Hypertree.Reductions.ChainPreimage
import all VCVio.CryptoFoundations.SyncSignatureAlg
import all HashSig.GXMSS.Security.Reductions.ChainPreimage
import all HashSig.GXMSS.Security.Reductions.ChainUndetectability

/-!
# Depth-one chain challenge and splice coordinates

These laws transport actual original-domain challenges, uniform global selectors and every
spliced prefix through the unique component coordinate. Transport of complete adaptive PRE
and UD experiments additionally requires matching the filtered signing state and observations.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash MeasureTheory ProbabilityTheory

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Forget exactly the unique component coordinate of one global positive chain position. -/
@[expose] def chainPositionEquiv :
    ChainPosition (singleShape h w v) ≃ GXMSS.Reductions.Guess h w v :=
  Equiv.prodCongr otsEquiv (Equiv.refl _)

/-- Global selection retains the original local epoch, chain label and positive-step index. -/
@[simp] theorem chainPositionEquiv_apply (selector : ChainPosition (singleShape h w v)) :
    chainPositionEquiv selector = (selector.1.2, selector.2) := rfl

/-- The depth-one PRE problem is the identical original-domain native hardness problem. -/
theorem chainPREProblem_single (hash : GXMSS.HashInstance PP T X H h w v) :
    Security.chainPREProblem (liftHash hash) = GXMSS.Reductions.chainPREProblem hash := rfl

/-- The depth-one UD problem preserves both native worlds and their original domain. -/
theorem chainUDProblem_single [SampleableType H]
    (hash : GXMSS.HashInstance PP T X H h w v) :
    Security.chainUDProblem (liftHash hash) = GXMSS.Reductions.chainUDProblem hash := rfl

/-- Each world's actual challenge response is unchanged by the full-coordinate observation. -/
theorem chainUD_response_single [SampleableType H]
    (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (selector : ChainPosition (singleShape h w v)) (world : SM_DT_UD_World) :
    SM_DT_UD_response world (Security.chainUDProblem (liftHash hash)) pp
        ((liftHash hash).chainTweak selector) =
      SM_DT_UD_response world (GXMSS.Reductions.chainUDProblem hash) pp
        (hash.chainTweak (chainPositionEquiv selector)) := rfl

/-- The global canonical total PRE fallback becomes the old leaf-zero, chain-zero fallback. -/
theorem canonicalPreimageFallback_single
    (starts : OTSPosition (singleShape h w v) → Fin v → H) (hv : 0 < v) :
    Security.canonicalPreimageFallback starts hv = startsEquiv starts 0 ⟨0, hv⟩ := rfl

/-- Reindexing the actual global uniform selector yields the old complete-tree selector law. -/
theorem sampleSelector_evalDistEq [NeZero v] [NeZero (2 ^ w - 1)]
    (hv : 0 < v) (hw : 0 < w) :
    chainPositionEquiv <$> Security.ChainMass.sampleSelector (singleShape h w v) hv hw =ᵈ
      ($ᵗ (GXMSS.Reductions.Guess h w v)) := by
  let : MeasurableSpace (ChainPosition (singleShape h w v)) := ⊤
  let : MeasurableSpace (GXMSS.Reductions.Guess h w v) := ⊤
  let : SampleableType (ChainPosition (singleShape h w v)) :=
    Security.ChainMass.selectorSampling _ hv hw
  apply EvalDistEq.of_evalDist_eq
  rw [evalDist_map_of_discrete]
  change (𝒟[($ᵗ (ChainPosition (singleShape h w v)))]).map chainPositionEquiv = _
  rw [SampleableType.evalDist_uniformSample, SampleableType.evalDist_uniformSample]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete chainPositionEquiv.bijective

/-- Every depth-one spliced prefix is the old complete-tree splice at the observed coordinate. -/
theorem splicePrefixes_single (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (selector : ChainPosition (singleShape h w v)) (answer : H)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (ep : Fin (2 ^ h)) (i : Fin v) (position : ℕ) :
    Security.ChainContinuation.splicePrefixes (liftHash hash) pp selector.1 selector.2.1
        selector.2.2.val answer starts (topTree _, ep) i position =
      if ep = selector.1.2 ∧ i = selector.2.1 then
        if position < selector.2.2.val + 1 then
          hash.chain pp ep i 0 position (startsEquiv starts ep i)
        else hash.chain pp ep i (selector.2.2.val + 1)
          (position - (selector.2.2.val + 1)) answer
      else hash.chain pp ep i 0 position (startsEquiv starts ep i) := by
  have heq : ((topTree (singleShape h w v), ep) : OTSPosition (singleShape h w v)) =
      selector.1 ↔ ep = selector.1.2 := by
    constructor
    · exact congrArg Prod.snd
    · intro hep
      exact Prod.ext (Subsingleton.elim _ _) hep
  simp only [Security.ChainContinuation.splicePrefixes,
    GXMSS.Reductions.ChainContinuation.spliceValue, heq,
    Security.ChainContinuation.chainFamily, componentHash_liftHash, startsEquiv_apply]
  split_ifs <;> rfl

/-- The endpoint-visible guard is exactly the old complete-opening strong-source guard at
depth one, including its behavior on arbitrary invalid or replayed signatures. -/
theorem cutValidityGuard_single [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (out : Security.Result PP H M R (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v))
    (hseed : out.pk.seed = out.sk.seed)
    (hroot : out.pk.root = componentRoot (liftHash hash) out.sk.seed out.sk.endpoints (topTree _))
    (word : Codeword v (2 ^ w))
    (hword : enc.value out.sk.seed out.forgery.2.1 out.forgery.2.2.bottom.randomizer
      (epochEquiv out.forgery.1) = some word) :
    Security.cutValidityGuard (liftHash hash) (familyOfEncoding enc) out.sk.seed out.sk.endpoints
        (Security.ChainContinuation.prepare (liftHash hash) (familyOfEncoding enc)
          (RetrySampling.iid K J).internal out.sk.seed out.sk.endpoints out.sk.upperCoins)
        out.forgery (out.history, out.bottomAttempts)
        ⟨bottomPosition _ out.forgery.1, bottomMessage out.forgery.1 out.forgery.2.1,
          out.forgery.2.2.bottom⟩ word =
      GXMSS.Reductions.gameOneObservation hash enc K (enrichedSourceObservation out) := by
  let : DecidableEq (Signature R H (singleShape h w v)) := Security.signatureDecidableEq
  have hpk : out.pk =
      ⟨componentRoot (liftHash hash) out.sk.seed out.sk.endpoints (topTree _), out.sk.seed⟩ := by
    calc
      out.pk = ⟨out.pk.root, out.pk.seed⟩ := rfl
      _ = _ := by rw [hseed, hroot]
  have hstrong := strongValid_observation hash enc K J (out.pk, out.forgery, out.history)
  unfold Security.cutValidityGuard
  change ((verify (liftHash hash) (familyOfEncoding enc)
      ⟨componentRoot (liftHash hash) out.sk.seed out.sk.endpoints (topTree _), out.sk.seed⟩
      out.forgery.1 out.forgery.2.1 out.forgery.2.2 &&
      SyncSignatureUnforgeability.strongFresh out.history out.forgery) && (_ : Bool)) = _
  rw [← hpk]
  change (SyncSignatureUnforgeability.strongValid
      (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J))
      (out.pk, out.forgery, out.history) && (_ : Bool)) = _
  rw [← hstrong]
  simp only [GXMSS.Reductions.gameOneObservation, GXMSS.Reductions.forgedLeaf?,
    enrichedSourceObservation, forgeryObservation, interactionObservation,
    secretKeyEquiv_endpoints, signatureEquiv_apply, hseed, hword,
    Option.map_some, Security.ChainContinuation.prepare,
    componentHash_liftHash, bottomPosition_eq, startsEquiv_apply]
  unfold GXMSS.Hypertree.Unforgeability.completedLeaf
  simp only [componentHash_liftHash, bottomPosition_eq]
  rfl

end GXMSS.Hypertree.SingleLayer
