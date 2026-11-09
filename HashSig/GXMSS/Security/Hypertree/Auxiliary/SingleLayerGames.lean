/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.SingleLayer
public import HashSig.GXMSS.Security.Hypertree.Reductions.ChainCutCollision
public import HashSig.GXMSS.Security.Reductions.TargetCollision
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
public import HashSig.GXMSS.Security.Reductions.MerkleCollision
public import HashSig.GXMSS.Security.Reductions.SameMessageChainCollision
public import HashSig.GXMSS.Security.Interval.Reductions.FullRange
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.TargetCounts
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses
import all HashSig.GXMSS.Security.Hypertree.Reductions.MerkleCollision
import all HashSig.GXMSS.Security.Reductions.TargetCollision
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
import all VCVio.CryptoFoundations.SyncSignatureAlg
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
import all HashSig.GXMSS.Hypertree.Scheme
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
import all HashSig.GXMSS.Security.Reductions.MerkleCollision
import all HashSig.GXMSS.Security.Reductions.SameMessageChainCollision

/-!
# Depth-one global target and witness correspondences

The full forest ledger becomes the ordinary complete-tree ledger in its actual issue order.
These laws retain collision orientation, exact lookup indices and total fallback inputs.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec TweakableHash
open GXMSS.Hypertree.Unforgeability GXMSS.Security

variable {PP T X H M R Coins : Type} {h w v : ℕ}

/-- The only component in the global issue order is the ordinary top tree. -/
theorem componentEnumeration_single (a : Fin (treeCount (singleShape h w v))) :
    componentEnumeration (singleShape h w v) a = topTree (singleShape h w v) := tree_eq_top _

/-- The global chain ledger is exactly the old epoch-major positive-step ledger. -/
theorem chainLedger_single (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (starts : OTSPosition (singleShape h w v) → Fin v → H) :
    chainLedger (liftHash hash) pp starts =
      GXMSS.Reductions.endpointTargets hash pp (startsEquiv starts) := by
  simp [chainLedger, componentEnumeration_single, componentChainTargets,
    startsEquiv, otsEquiv]
  rfl

/-- The sole global Merkle traversal has the ordinary left-right-parent issue order. -/
theorem merkleLedger_single (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (ends : OTSPosition (singleShape h w v) → Fin v → H) :
    merkleLedger (liftHash hash) pp ends =
      GXMSS.Reductions.merkleTargets hash pp (startsEquiv ends) := by
  simp [merkleLedger, componentEnumeration_single, componentMerkleTargets,
    startsEquiv, otsEquiv]
  rfl

/-- Complete accepted registration retains chains followed by the full ordered tree. -/
theorem setupLedger_single (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (starts ends : OTSPosition (singleShape h w v) → Fin v → H) :
    setupLedger (liftHash hash) pp starts ends =
      GXMSS.Reductions.endpointTargets hash pp (startsEquiv starts) ++
        GXMSS.Reductions.merkleTargets hash pp (startsEquiv ends) := by
  rw [setupLedger, chainLedger_single, merkleLedger_single]

/-- The canonical Merkle fallback specializes to the ordinary leaf-zero endpoint vector. -/
theorem merkleFallbackInput_single (hash : GXMSS.HashInstance PP T X H h w v)
    (ends : OTSPosition (singleShape h w v) → Fin v → H) :
    merkleFallbackInput (liftHash hash) ends = hash.vectorInput (startsEquiv ends 0) := rfl

/-- Registered collisions keep the same index and extracted second input. -/
theorem selectCollision_single [DecidableEq T] [DecidableEq X]
    (ledger : List (T × X)) (collision : HashCollision T X) :
    selectCollision ledger collision =
      (GXMSS.Reductions.registeredIndex ledger collision.tweak collision.first,
        collision.second) := rfl

/-- Global safe chain capacity specializes to the old complete-tree challenge capacity. -/
theorem chainCapacity_single : chainCapacity (singleShape h w v) = 2 ^ h * v * 2 ^ w := by
  simp [chainCapacity]

/-- Global safe Merkle capacity specializes to the old complete-tree challenge capacity. -/
theorem merkleCapacity_single :
    merkleCapacity (singleShape h w v) = 2 * (2 ^ h) * v * 2 ^ w := by
  simp [merkleCapacity]

/-- The selected layer is deterministically the ordinary bottom component. -/
theorem sourceCandidate?_single [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (out : Security.Result PP H M R Coins (singleShape h w v)) :
    sourceCandidate? (liftHash hash) (familyOfEncoding enc) out =
      some ⟨bottomPosition _ out.forgery.1, bottomMessage out.forgery.1 out.forgery.2.1,
        out.forgery.2.2.bottom⟩ := rfl

/-- Every depth-one decoded component reads the ordinary forged message and randomizer. -/
theorem sourceDecoded?_single [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (out : Security.Result PP H M R Coins (singleShape h w v)) :
    sourceDecoded? (liftHash hash) (familyOfEncoding enc) out = (do
      let word ← enc.value out.sk.seed out.forgery.2.1 out.forgery.2.2.bottom.randomizer
        (epochEquiv out.forgery.1)
      pure (⟨bottomPosition _ out.forgery.1, bottomMessage out.forgery.1 out.forgery.2.1,
        out.forgery.2.2.bottom⟩, word)) := by
  rcases out with ⟨pk, sk, ⟨ep, msg, sig⟩, history, upper, bottom⟩
  change (do
    let word ← enc.value sk.seed (messageEquiv (bottomPosition _ ep) (bottomMessage ep msg))
      sig.bottom.randomizer (bottomPosition _ ep).2
    pure ((⟨bottomPosition _ ep, bottomMessage ep msg, sig.bottom⟩ :
      ComponentCandidate M R H (singleShape h w v)), word)) = _
  rw [messageEquiv_bottomMessage]
  rw [show (bottomPosition (singleShape h w v) ep).2 =
    epochEquiv ep from otsEquiv_bottomPosition ep]

/-- The global Merkle finder is the existing ordinary finder on the same complete opening. -/
theorem sourceMerkleWitness?_single [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (out : Security.Result PP H M R Coins (singleShape h w v)) :
    sourceMerkleWitness? (liftHash hash) (familyOfEncoding enc) out = (do
      let word ← enc.value out.sk.seed out.forgery.2.1 out.forgery.2.2.bottom.randomizer
        (epochEquiv out.forgery.1)
      hash.findMerkleCollision out.sk.seed (epochEquiv out.forgery.1)
        (startsEquiv out.sk.endpoints (epochEquiv out.forgery.1))
        (fun i => hash.chain out.sk.seed (epochEquiv out.forgery.1) i (word i)
          (2 ^ w - 1 - (word i).val) (out.forgery.2.2.bottom.ots i))
        (hash.authPath out.sk.seed (startsEquiv out.sk.endpoints) (epochEquiv out.forgery.1))
        out.forgery.2.2.bottom.path) := by
  rcases out with ⟨pk, sk, ⟨ep, msg, sig⟩, history, upper, bottom⟩
  rw [sourceMerkleWitness?, sourceDecoded?_single]
  dsimp only
  cases enc.value sk.seed msg sig.bottom.randomizer (epochEquiv ep) with
  | none => rfl
  | some word =>
    change hash.findMerkleCollision sk.seed (bottomPosition _ ep).2
      (sk.endpoints (bottomPosition _ ep))
      (fun i => hash.chain sk.seed (bottomPosition _ ep).2 i (word i)
        (2 ^ w - 1 - (word i).val) (sig.bottom.ots i))
      (hash.authPath sk.seed (fun e => sk.endpoints ((bottomPosition _ ep).1, e))
        (bottomPosition _ ep).2) sig.bottom.path = _
    rw [bottomPosition_eq]
    rfl

/-- Observe one total primitive candidate using the raw key retained by the native source. -/
@[expose] def sourceCollisionObservation [DecidableEq T] [DecidableEq X] [DecidableEq H]
    {S : Shape} (hash : HashInstance PP T X H S)
    (ledger : PP → (OTSPosition S → Fin S.v → H) →
      (OTSPosition S → Fin S.v → H) → List (T × X))
    (fallbackInput : H → (OTSPosition S → Fin S.v → H) → X)
    (find : Security.Result PP H M R Coins S → Option (HashCollision T X))
    (fallback : H) (out : Security.Result PP H M R Coins S) : Bool :=
  let registered := ledger out.sk.seed out.sk.starts out.sk.endpoints
  candidateCheck hash out.sk.seed registered
    (witnessCandidate registered (fallbackInput fallback out.sk.endpoints) (find out))

/-- The actual registered collision execution is the enriched native source with its independent
total-fallback draw retained. The law preserves all extraction failures and accidental wins. -/
theorem collisionProgram_source_evalDistEq [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] {S : Shape}
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (ledger : PP → (OTSPosition S → Fin S.v → H) →
      (OTSPosition S → Fin S.v → H) → List (T × X))
    (fallbackInput : H → (OTSPosition S → Fin S.v → H) → X)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X)) :
    collisionProgram hash family sampling adv ledger fallbackInput find =ᵈ
      (do
        let fallback ← ($ᵗ H : ProbComp H)
        sourceCollisionObservation hash ledger fallbackInput find fallback <$>
          Security.sourceProgram hash family sampling adv) := by
  let : MeasurableSpace Bool := ⊤
  apply EvalDistEq.of_evalDist_eq
  unfold collisionProgram
  rw [OracleComp.evalDist_bind_bind_swap]
  apply OracleComp.evalDist_bind_congr_of_support
  intro fallback _
  simp only [Security.sourceProgram, keygen, map_bind, bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_congr_of_support
  intro pp _
  apply OracleComp.evalDist_bind_congr_of_support
  intro starts _
  apply OracleComp.evalDist_bind_congr_of_support
  intro coins _
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_congr_of_support
  intro out hout
  have hk := Security.runWithKeys_support_keys hash family sampling adv
    (keys hash pp starts coins).1 (keys hash pp starts coins).2 out hout
  simp only [sourceCollisionObservation, hk.2.1, keys]

private def ordinaryMerkleObservation [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (fallback : H) (out : GXMSS.Reductions.Result PP H M R h v) : Bool :=
  let ledger := GXMSS.Reductions.endpointTargets hash out.sk.seed out.sk.starts ++
    GXMSS.Reductions.merkleTargets hash out.sk.seed out.sk.endpoints
  let state : GXMSS.Reductions.TCRKeyState PP T X H h v :=
    ⟨out.sk.starts, out.sk.endpoints, hash.merkleRoot out.sk.seed out.sk.endpoints,
      ledger, fallback⟩
  GXMSS.Unforgeability.merkleCandidateWins hash out.sk.seed ledger
    (GXMSS.Unforgeability.merkleCandidate hash enc state out.sk.seed out)

/-- The total global Merkle decision, including failed extraction, is the old decision on the
same raw keys, full signature, opening, ledger index and fallback vector. -/
private theorem sourceMerkleObservation_single [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (fallback : H) (out : Security.Result PP H M R Coins (singleShape h w v))
    (hseed : out.pk.seed = out.sk.seed) :
    sourceCollisionObservation (liftHash hash) (setupLedger (liftHash hash))
      (fun _ ends => merkleFallbackInput (liftHash hash) ends)
      (sourceMerkleWitness? (liftHash hash) (familyOfEncoding enc)) fallback out =
      ordinaryMerkleObservation hash enc fallback (enrichedSourceObservation out) := by
  rw [sourceCollisionObservation, setupLedger_single, sourceMerkleWitness?_single,
    merkleFallbackInput_single]
  rcases out with ⟨pk, sk, ⟨ep, msg, sig⟩, history, upper, bottom⟩
  dsimp only at hseed ⊢
  unfold ordinaryMerkleObservation GXMSS.Unforgeability.merkleCandidate
    GXMSS.Reductions.forgedLeaf? enrichedSourceObservation forgeryObservation
  simp only [secretKeyEquiv_seed, secretKeyEquiv_starts, secretKeyEquiv_endpoints,
    signatureEquiv_apply, hseed]
  cases hw : enc.value sk.seed msg sig.bottom.randomizer (epochEquiv ep) with
  | none => rfl
  | some word =>
    simp only [Option.map_some]
    change candidateCheck (liftHash hash) sk.seed _ (witnessCandidate _ _
      (hash.findMerkleCollision sk.seed (epochEquiv ep)
        (startsEquiv sk.endpoints (epochEquiv ep))
        (fun i => hash.chain sk.seed (epochEquiv ep) i (word i)
          (2 ^ w - 1 - (word i).val) (sig.bottom.ots i))
        (hash.authPath sk.seed (startsEquiv sk.endpoints) (epochEquiv ep)) sig.bottom.path)) = _
    cases hash.findMerkleCollision sk.seed (epochEquiv ep)
      (startsEquiv sk.endpoints (epochEquiv ep))
      (fun i => hash.chain sk.seed (epochEquiv ep) i (word i)
        (2 ^ w - 1 - (word i).val) (sig.bottom.ots i))
      (hash.authPath sk.seed (startsEquiv sk.endpoints) (epochEquiv ep)) sig.bottom.path <;> rfl

private theorem ordinaryMerkleProgram_source_evalDistEq [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Unforgeability.merkleCoupledProgram hash enc K adv =ᵈ
      (do let fallback ← ($ᵗ H : ProbComp H)
          ordinaryMerkleObservation hash enc fallback <$>
            GXMSS.Reductions.sourceProgram hash enc K adv) := by
  let : MeasurableSpace Bool := ⊤
  apply EvalDistEq.of_evalDist_eq
  unfold GXMSS.Unforgeability.merkleCoupledProgram
  rw [OracleComp.evalDist_bind_bind_swap]
  apply OracleComp.evalDist_bind_congr_of_support
  intro fallback _
  simp only [GXMSS.Reductions.sourceProgram, GXMSS.keygen, map_bind, bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_congr_of_support
  intro pp _
  apply OracleComp.evalDist_bind_congr_of_support
  intro starts _
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_congr_of_support
  intro out hout
  have hk := GXMSS.Reductions.runWithKeys_support_keys hash enc K adv
    (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 out hout
  simp only [ordinaryMerkleObservation, hk.2, GXMSS.keys]

/-- The actual named global Merkle experiment has the old entire Boolean output law at depth
one. Registration, extraction failure, fallback candidates and accidental wins are retained. -/
theorem merkleTargetCollisionExperiment_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Experiment (merkleTargetCollisionReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) adv) =ᵈ
      SM_DT_TCR_Experiment (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv
        (adversaryToOrdinary adv)) := by
  rw [merkleTargetCollisionReduction, forestCollisionReduction_experiment
    (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) adv _ hv]
  unfold forestCollisionProgram
  rw [GXMSS.Unforgeability.merkleExperiment_eq_coupled]
  apply EvalDistEq.trans (collisionProgram_source_evalDistEq _ _ _ _ _ _ _)
  apply EvalDistEq.trans _ (ordinaryMerkleProgram_source_evalDistEq hash enc K
    (adversaryToOrdinary adv)).symm
  apply EvalDistEq.bind_right
  intro fallback
  have hs := (sourceProgram_iid_evalDistEq hash enc K J adv).map
    (ordinaryMerkleObservation hash enc fallback)
  apply EvalDistEq.trans _ hs
  let : MeasurableSpace Bool := ⊤
  apply EvalDistEq.of_evalDist_eq
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply OracleComp.evalDist_bind_congr_of_support
  intro out hout
  rw [sourceMerkleObservation_single hash enc fallback out
    (Security.sourceProgram_support_seed_eq _ _ _ _ out hout)]

/-- The Merkle advantage specializes by its complete native Boolean measure. -/
theorem merkleTargetCollisionAdvantage_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Advantage (merkleTargetCollisionReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) adv) =
      SM_DT_TCR_Advantage (GXMSS.Reductions.merkleTargetCollisionReduction hash enc K hv
        (adversaryToOrdinary adv)) := by
  exact congrArg (fun measure => measure {true})
    (merkleTargetCollisionExperiment_single hash enc K J hv adv).evalDist_eq

/-- At depth one, the raw private bottom reference materializes exactly the full-history bottom
signature. In particular no successful raw result is hidden by an internal certificate failure. -/
theorem referenceSignature_single [SampleableType H]
    (hash : HashInstance PP T X H (singleShape h w v))
    (family : EncodingFamily PP M R H (singleShape h w v)) (sampling : RetrySampling R)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (out : Security.Result PP H M R sampling.internal.Coins (singleShape h w v))
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv))
    (ep : Epoch (singleShape h w v)) :
    Security.referenceSignatureAt hash out (bottomPosition _ ep) =
      (out.history ep).bind (fun entry => entry.2.map signatureEquiv) := by
  classical
  let history : Epoch (singleShape h w v) → Option (M × Option (Signature R H
    (singleShape h w v))) := out.history
  change Security.referenceSignatureAt hash out (bottomPosition _ ep) =
    (history ep).bind (fun entry => entry.2.map signatureEquiv)
  cases href : Security.referenceAt hash out (bottomPosition _ ep) with
  | none =>
    have hhistory : history ep = none := by
      cases hh : history ep with
      | none => rfl
      | some entry =>
        obtain ⟨attempt, ha, hep, _⟩ := sourceProgram_history_has_attempt hash family sampling
          adv out hout ep entry.1 entry.2 hh
        have hmem : (⟨bottomPosition _ attempt.epoch, bottomMessage attempt.epoch attempt.message,
            attempt.result.output⟩ : Security.FamilyEncoding.Record M H R (singleShape h w v)) ∈
            Security.bottomLedger out.bottomAttempts := List.mem_map.mpr ⟨attempt, ha, rfl⟩
        unfold Security.referenceAt at href
        rw [dite_eq_left (show (bottomPosition (singleShape h w v) ep).1.1.val = 0 from rfl)]
          at href
        have hn := (List.find?_eq_none.mp href) _ hmem
        exact False.elim (hn (by simp only [hep, decide_true]))
    simp only [Security.referenceSignatureAt, href, hhistory, Option.bind_none]
  | some entry =>
    obtain ⟨attempt, ha, hp, he⟩ := Security.referenceAt_bottom_attempt hash out
      (bottomPosition _ ep) rfl entry href
    have hep : attempt.epoch = ep := positionAt_bottom_injective _ hp
    obtain ⟨coins, _, hactual, hhistory⟩ :=
      Security.sourceProgram_attempts_match_history hash family sampling adv out hout attempt ha
    rw [hep] at hactual hhistory
    change history ep = some (attempt.message,
      signWithCoins hash family sampling out.sk ep attempt.message coins) at hhistory
    rw [hhistory]
    simp only [Security.referenceSignatureAt, href, Option.bind_some]
    subst entry
    change attempt.result.output.map (componentSignature hash out.sk (bottomPosition _ ep)) = _
    rw [hactual]
    exact (signWithCoins_single hash family sampling out.sk ep attempt.message coins).symm

/-- A successful private reference at the unique layer is exactly the successful full-history
pair, including its application message and complete canonical component signature. -/
theorem referenceAt_success_history_single [SampleableType H]
    (hash : HashInstance PP T X H (singleShape h w v))
    (family : EncodingFamily PP M R H (singleShape h w v)) (sampling : RetrySampling R)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (out : Security.Result PP H M R sampling.internal.Coins (singleShape h w v))
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv))
    (ep : Epoch (singleShape h w v))
    (entry : Security.FamilyEncoding.Record M H R (singleShape h w v))
    (wr : Codeword v (2 ^ w) × R)
    (href : Security.referenceAt hash out (bottomPosition _ ep) = some entry)
    (hresult : entry.result = some wr) :
    out.history ep = some (messageEquiv entry.position entry.message,
      some (signatureEquiv.symm (componentSignature hash out.sk (bottomPosition _ ep) wr))) := by
  classical
  obtain ⟨attempt, ha, hp, he⟩ := Security.referenceAt_bottom_attempt hash out
    (bottomPosition _ ep) rfl entry href
  have hep : attempt.epoch = ep := positionAt_bottom_injective _ hp
  have hquery : (⟨entry.position, entry.message⟩ : Security.FamilyEncoding.Query M H
      (singleShape h w v)) = ⟨bottomPosition _ ep, bottomMessage ep attempt.message⟩ := by
    rw [he]
    exact congrArg (fun e : Epoch (singleShape h w v) =>
      (⟨bottomPosition _ e, bottomMessage e attempt.message⟩ :
        Security.FamilyEncoding.Query M H (singleShape h w v))) hep
  have hh := Security.history_of_referenceAt_bottom_success hash family sampling adv out hout ep
    attempt.message entry wr Fin.elim0 href hresult hquery (fun i => i.elim0)
  have hm : messageEquiv entry.position entry.message = attempt.message := by
    rw [he]
    exact messageEquiv_bottomMessage attempt.epoch attempt.message
  rw [hm]
  exact hh

private theorem history_no_success_of_reference_none [SampleableType H]
    (hash : HashInstance PP T X H (singleShape h w v))
    (family : EncodingFamily PP M R H (singleShape h w v)) (sampling : RetrySampling R)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (out : Security.Result PP H M R sampling.internal.Coins (singleShape h w v))
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv))
    (ep : Epoch (singleShape h w v))
    (h : Security.referenceSignatureAt hash out (bottomPosition _ ep) = none) :
    (out.history ep).bind Prod.snd = none := by
  have hh := (referenceSignature_single hash family sampling adv out hout ep).symm.trans h
  cases hx : out.history ep with
  | none => rfl
  | some entry =>
    rcases entry with ⟨msg, answer⟩
    cases answer with
    | none => rfl
    | some sig =>
      simp only [hx, Option.bind_some, Option.map_some] at hh
      cases hh

private theorem sourceSameWordWitness_none_of_reference_none [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (out : Security.Result PP H M R Coins (singleShape h w v))
    (hnone : Security.referenceSignatureAt (liftHash hash) out
      (bottomPosition _ out.forgery.1) = none) :
    sourceSameWordWitness? (liftHash hash) (familyOfEncoding enc) out = none := by
  rw [sourceSameWordWitness?, sourceDecoded?_single]
  cases enc.value out.sk.seed out.forgery.2.1 out.forgery.2.2.bottom.randomizer
      (epochEquiv out.forgery.1) with
  | none => rfl
  | some word =>
    change (Security.referenceAt (liftHash hash) out (bottomPosition _ out.forgery.1)).bind _ = none
    cases href : Security.referenceAt (liftHash hash) out (bottomPosition _ out.forgery.1) with
    | none => rfl
    | some entry =>
      change entry.result.bind _ = none
      cases hr : entry.result with
      | none => rfl
      | some wr =>
        simp only [Security.referenceSignatureAt, href, Option.bind_some, hr,
          Option.map_some] at hnone
        cases hnone

private theorem firstChainCandidate_single [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (out : Security.Result PP H M R sampling.internal.Coins (singleShape h w v))
    (hout : out ∈ support (Security.sourceProgram (liftHash hash) (familyOfEncoding enc)
      sampling adv)) (fallback : H) :
    witnessCandidate (chainLedger (liftHash hash) out.sk.seed out.sk.starts)
      (hash.digestInput fallback)
      (sourceSameWordWitness? (liftHash hash) (familyOfEncoding enc) out) =
      GXMSS.Unforgeability.firstChainCandidate hash enc
        ⟨startsEquiv out.sk.starts, startsEquiv out.sk.endpoints, fallback,
          GXMSS.Reductions.endpointTargets hash out.sk.seed (startsEquiv out.sk.starts), fallback⟩
        out.sk.seed (enrichedSourceObservation out) := by
  rcases out with ⟨pk, sk, ⟨epoch, message, signature⟩, history, upper, bottom⟩
  change Epoch (singleShape h w v) → Option (M × Option (Signature R H (singleShape h w v)))
    at history
  let out : Security.Result PP H M R sampling.internal.Coins (singleShape h w v) :=
    ⟨pk, sk, (epoch, message, signature), history, upper, bottom⟩
  change out ∈ support
    (Security.sourceProgram (liftHash hash) (familyOfEncoding enc) sampling adv) at hout
  let ep := out.forgery.1
  let p := bottomPosition (singleShape h w v) ep
  have he : p.2 = epochEquiv ep := otsEquiv_bottomPosition ep
  have hp : p.1 = topTree (singleShape h w v) := tree_eq_top _
  rw [chainLedger_single]
  cases href : Security.referenceAt (liftHash hash) out p with
  | none =>
    have hnone : Security.referenceSignatureAt (liftHash hash) out p = none := by
      simp only [Security.referenceSignatureAt, href, Option.bind_none]
    have hh := history_no_success_of_reference_none (liftHash hash) (familyOfEncoding enc)
      sampling adv out hout ep hnone
    rw [sourceSameWordWitness_none_of_reference_none hash enc out hnone, witnessCandidate]
    unfold GXMSS.Unforgeability.firstChainCandidate enrichedSourceObservation
      forgeryObservation historyObservation
    simp only [Equiv.symm_apply_apply, signatureEquiv_apply]
    cases hx : out.history ep with
    | none => simp_all [out, ep]
    | some pair =>
      rcases pair with ⟨msg, answer⟩
      cases answer with
      | none => simp_all [out, ep]
      | some sig =>
        simp only [hx, Option.bind_some] at hh
        cases hh
  | some entry =>
    cases hr : entry.result with
    | none =>
      have hnone : Security.referenceSignatureAt (liftHash hash) out p = none := by
        simp only [Security.referenceSignatureAt, href, Option.bind_some, hr, Option.map_none]
      have hh := history_no_success_of_reference_none (liftHash hash) (familyOfEncoding enc)
        sampling adv out hout ep hnone
      rw [sourceSameWordWitness_none_of_reference_none hash enc out hnone, witnessCandidate]
      unfold GXMSS.Unforgeability.firstChainCandidate enrichedSourceObservation
        forgeryObservation historyObservation
      simp only [Equiv.symm_apply_apply, signatureEquiv_apply]
      cases hx : out.history ep with
      | none => simp_all [out, ep]
      | some pair =>
        rcases pair with ⟨msg, answer⟩
        cases answer with
        | none => simp_all [out, ep]
        | some sig =>
          simp only [hx, Option.bind_some] at hh
          cases hh
    | some wr =>
      have hh := referenceAt_success_history_single (liftHash hash) (familyOfEncoding enc)
        sampling adv out hout ep entry wr href hr
      have hv := Security.referenceAt_value_eq_some (liftHash hash) (familyOfEncoding enc)
        sampling adv out hout p entry href wr.1 wr.2 hr
      have hep := Security.referenceAt_position (liftHash hash) out p entry href
      rw [familyOfEncoding_value] at hv
      have hleaf : entry.position.2 = epochEquiv ep := (congrArg Prod.snd hep).trans he
      rw [hleaf] at hv
      unfold sourceSameWordWitness?
      rw [sourceDecoded?_single]
      cases hf : enc.value out.sk.seed out.forgery.2.1 out.forgery.2.2.bottom.randomizer
          (epochEquiv ep) with
      | none =>
        change (0, hash.digestInput fallback) = _
        unfold GXMSS.Unforgeability.firstChainCandidate enrichedSourceObservation
          forgeryObservation historyObservation
        simp only [Equiv.symm_apply_apply]
        dsimp only [out, ep, p] at hh hv hf ⊢
        rw [hh]
        simp only [Option.map_some, Equiv.apply_symm_apply, componentSignature_eq,
          otsEquiv_bottomPosition, GXMSS.signatureOfWord, signatureEquiv_apply]
        rw [hv, hf]
      | some word =>
        change witnessCandidate _ _ ((Security.referenceAt (liftHash hash) out p).bind _) = _
        rw [href]
        change witnessCandidate _ _ (entry.result.bind _) = _
        rw [hr]
        unfold GXMSS.Unforgeability.firstChainCandidate enrichedSourceObservation
          forgeryObservation historyObservation
        simp only [Equiv.symm_apply_apply]
        dsimp only [out, ep, p] at hh hv hf ⊢
        rw [hh]
        simp only [Option.map_some, Equiv.apply_symm_apply, componentSignature_eq,
          otsEquiv_bottomPosition, GXMSS.signatureOfWord, signatureEquiv_apply]
        rw [hv, hf]
        change witnessCandidate _ _ (if wr.1 = word then _ else none) =
          (if wr.1 = word then _ else _)
        split_ifs with hword
        · let canonical := GXMSS.signatureOfWord hash (secretKeyEquiv _ sk) (epochEquiv epoch) wr
          change witnessCandidate _ _
            ((findUnequalCoordinate canonical.ots signature.bottom.ots).bind _) = _
          cases hi : findUnequalCoordinate canonical.ots signature.bottom.ots with
          | none =>
            simp only [canonical, GXMSS.signatureOfWord] at hi
            rw [hi]
            rfl
          | some i =>
            simp only [canonical, GXMSS.signatureOfWord] at hi
            rw [hi]
            simp only [Option.bind_some, componentHash_liftHash]
            rw [show (bottomPosition (singleShape h w v) epoch).2 = epochEquiv epoch from
              otsEquiv_bottomPosition epoch]
            change witnessCandidate _ _ ((hash.findChainCollision sk.seed (epochEquiv epoch) i
              (wr.1 i) (2 ^ w - 1 - (wr.1 i).val) (canonical.ots i)
              (signature.bottom.ots i)).bind _) = _
            cases hd : hash.findChainCollision sk.seed (epochEquiv epoch) i (wr.1 i)
                (2 ^ w - 1 - (wr.1 i).val) (canonical.ots i) (signature.bottom.ots i) <;>
              (simp only [canonical, GXMSS.signatureOfWord] at hd; rw [hd]; rfl)
        · rfl

private def ordinaryFirstChainObservation [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (fallback : H) (out : GXMSS.Reductions.Result PP H M R h v) : Bool :=
  let ledger := GXMSS.Reductions.endpointTargets hash out.sk.seed out.sk.starts
  let state : GXMSS.Reductions.TCRKeyState PP T X H h v :=
    ⟨out.sk.starts, out.sk.endpoints, fallback, ledger, fallback⟩
  GXMSS.Unforgeability.firstChainCandidateWins hash out.sk.seed ledger
    (GXMSS.Unforgeability.firstChainCandidate hash enc state out.sk.seed out)

private theorem ordinaryFirstProgram_source_evalDistEq [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : GXMSS.Reductions.SchemeAdversary PP H M R h v) :
    GXMSS.Unforgeability.firstChainCoupledProgram hash enc K adv =ᵈ
      (do let fallback ← ($ᵗ H : ProbComp H)
          ordinaryFirstChainObservation hash enc fallback <$>
            GXMSS.Reductions.sourceProgram hash enc K adv) := by
  let : MeasurableSpace Bool := ⊤
  apply EvalDistEq.of_evalDist_eq
  unfold GXMSS.Unforgeability.firstChainCoupledProgram
  rw [OracleComp.evalDist_bind_bind_swap]
  apply OracleComp.evalDist_bind_congr_of_support
  intro fallback _
  simp only [GXMSS.Reductions.sourceProgram, GXMSS.keygen, map_bind, bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_congr_of_support
  intro pp _
  apply OracleComp.evalDist_bind_congr_of_support
  intro starts _
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_congr_of_support
  intro out hout
  have hk := GXMSS.Reductions.runWithKeys_support_keys hash enc K adv
    (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 out hout
  simp only [ordinaryFirstChainObservation, hk.2, GXMSS.keys]

/-- The actual same-message chain reduction preserves the old complete Boolean experiment,
including the total digest fallback after every unsuccessful extraction. -/
theorem sameMessageChainTargetCollisionExperiment_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Experiment (sameMessageChainTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) adv) =ᵈ
      SM_DT_TCR_Experiment (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K
        (adversaryToOrdinary adv)) := by
  rw [sameMessageChainTargetCollisionReduction, chainCollisionReduction_experiment]
  unfold chainCollisionProgram
  rw [GXMSS.Unforgeability.firstChainExperiment_eq_coupled]
  apply EvalDistEq.trans (collisionProgram_source_evalDistEq _ _ _ _ _ _ _)
  apply EvalDistEq.trans _ (ordinaryFirstProgram_source_evalDistEq hash enc K
    (adversaryToOrdinary adv)).symm
  apply EvalDistEq.bind_right
  intro fallback
  have hs := (sourceProgram_iid_evalDistEq hash enc K J adv).map
    (ordinaryFirstChainObservation hash enc fallback)
  apply EvalDistEq.trans _ hs
  let : MeasurableSpace Bool := ⊤
  apply EvalDistEq.of_evalDist_eq
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply OracleComp.evalDist_bind_congr_of_support
  intro out hout
  unfold sourceCollisionObservation
  dsimp only
  rw [show (liftHash hash).digestInput = hash.digestInput from rfl]
  rw [firstChainCandidate_single hash enc (RetrySampling.iid K J) adv out hout fallback,
    chainLedger_single]
  rfl

/-- Equality of the entire native B1 experiment yields equality of its advantage. -/
theorem sameMessageChainTargetCollisionAdvantage_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Advantage (sameMessageChainTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) adv) =
      SM_DT_TCR_Advantage (GXMSS.Reductions.firstChainTargetCollisionReduction hash enc K
        (adversaryToOrdinary adv)) := by
  exact congrArg (fun measure => measure {true})
    (sameMessageChainTargetCollisionExperiment_single hash enc K J adv).evalDist_eq

/-- The named global Merkle experiment also transports to the retained full-range interval
endpoint, using its proved complete-tree experiment equality. -/
theorem merkleTargetCollisionExperiment_full_single [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (hv : 0 < v) (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Experiment (merkleTargetCollisionReduction (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) adv) =ᵈ
      SM_DT_TCR_Experiment (GXMSS.Interval.Unforgeability.merkleTargetCollisionAdversary
        hash enc K (GXMSS.IntervalMerkle.Interval.full h) hv (adversaryToOrdinary adv)) := by
  rw [GXMSS.Interval.Unforgeability.merkleTargetCollisionExperiment_full]
  exact merkleTargetCollisionExperiment_single hash enc K J hv adv

/-- The named global B1 experiment transports to the retained full-range interval endpoint. -/
theorem sameMessageChainTargetCollisionExperiment_full_single
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    SM_DT_TCR_Experiment (sameMessageChainTargetCollisionReduction (liftHash hash)
      (familyOfEncoding enc) (RetrySampling.iid K J) adv) =ᵈ
      SM_DT_TCR_Experiment
        (GXMSS.Interval.Reductions.Chain.sameMessageRandomizerChainTargetCollisionReduction
          hash enc K (GXMSS.IntervalMerkle.Interval.full h) (adversaryToOrdinary adv)) := by
  rw [GXMSS.Interval.Unforgeability.sameMessageRandomizerChainTargetCollisionExperiment_full]
  exact sameMessageChainTargetCollisionExperiment_single hash enc K J adv

end GXMSS.Hypertree.SingleLayer
