/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Scheme
import all HashSig.GXMSS.Hypertree.Scheme
import all HashSig.GXMSS.Scheme
import all VCVio.EvalDist.EvalDistEq
import all VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# The depth-one hypertree specialization

The single layer has one component, no internal certificates and exactly the ordinary GXMSS
leaf coordinates. These maps retain the existing hash, raw keys, signature and encoding domains.
IID retry transport is stated as a returned-output distribution law, preserving exhaustion.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp MeasureTheory ProbabilityTheory

/-- A single ordinary GXMSS tree viewed as a positive-depth hypertree. -/
@[expose, reducible] def singleShape (h w v : ℕ) : Shape := ⟨1, h, w, v, by decide⟩

variable {PP T X H M R Coins : Type} {h w v : ℕ}

/-- A depth-one forest contains exactly one Merkle tree. -/
@[simp] theorem treeCount_single : treeCount (singleShape h w v) = 1 :=
  treeCount_depth_one _ rfl

/-- Every ordinary leaf contributes one one-time key. -/
@[simp] theorem otsCount_single : otsCount (singleShape h w v) = 2 ^ h := by
  simp [otsCount, Shape.branching]

/-- A depth-one forest has no private internal certification requests. -/
@[simp] theorem upperCount_single : upperCount (singleShape h w v) = 0 := by
  simp [upperCount]

/-- The exact positive-chain target count specializes without a component multiplier. -/
@[simp] theorem chainCount_single :
    chainCount (singleShape h w v) = 2 ^ h * v * (2 ^ w - 1) := by
  simp [chainCount]

/-- The only layer is the bottom layer. -/
theorem layer_zero (p : TreePosition (singleShape h w v)) : p.1.val = 0 := by
  have hp := p.1.isLt
  change p.1.val < 1 at hp
  omega

/-- The sole component is the canonical top tree. -/
theorem tree_eq_top (p : TreePosition (singleShape h w v)) :
    p = topTree (singleShape h w v) :=
  (eq_topTree_iff _ p).2 (layer_zero p)

instance : Subsingleton (TreePosition (singleShape h w v)) where
  allEq p q := (tree_eq_top p).trans (tree_eq_top q).symm

instance : IsEmpty (UpperPosition (singleShape h w v)) where
  false p := p.property (layer_zero p.val.1)

/-- Global depth-one epochs have exactly the ordinary GXMSS epoch bound. -/
@[expose] def epochEquiv : Epoch (singleShape h w v) ≃ Fin (2 ^ h) :=
  finCongr (by simp)

/-- The global epoch representation map preserves its natural value. -/
@[simp] theorem epochEquiv_val (ep : Epoch (singleShape h w v)) :
    (epochEquiv ep).val = ep.val := rfl

/-- Forget the unique component coordinate of a one-time signing key. -/
@[expose] def otsEquiv : OTSPosition (singleShape h w v) ≃ Fin (2 ^ h) where
  toFun p := p.2
  invFun e := (topTree _, e)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl

/-- Forget the unique component coordinate of a finite Merkle address. -/
@[expose] def treeAddressEquiv :
    (TreePosition (singleShape h w v) × Fin (h + 1) × Fin (2 ^ h)) ≃
      (Fin (h + 1) × Fin (2 ^ h)) where
  toFun p := p.2
  invFun t := (topTree _, t)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl

/-- Lift an existing common hash without changing its seed, inputs or local tweaks. -/
@[expose] def liftHash (hash : GXMSS.HashInstance PP T X H h w v) :
    HashInstance PP T X H (singleShape h w v) where
  thf := hash.thf
  digestInput := hash.digestInput
  pairInput := hash.pairInput
  vectorInput := hash.vectorInput
  chainTweak := (Equiv.prodCongr otsEquiv
    (Equiv.refl (Fin v × Fin (2 ^ w - 1)))).toEmbedding.trans hash.chainTweak
  treeTweak := treeAddressEquiv.toEmbedding.trans hash.treeTweak
  chain_ne_tree _ _ := hash.chain_ne_tree _ _

/-- Restricting the lifted hash to the unique component recovers the old interface exactly. -/
@[simp] theorem componentHash_liftHash (hash : GXMSS.HashInstance PP T X H h w v)
    (p : TreePosition (singleShape h w v)) : (liftHash hash).componentHash p = hash := by
  cases hash
  rfl

/-- Every depth-one message fibre is the original application-message type. -/
@[expose] def messageEquiv (p : OTSPosition (singleShape h w v)) :
    Message (singleShape h w v) M H p ≃ M :=
  Equiv.cast (by simp [Message])

/-- Capture the ordinary epoch in each coordinate's component encoding. -/
@[expose] def familyOfEncoding
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) :
    EncodingFamily PP M R H (singleShape h w v) where
  component p :=
    { code := enc.code
      incomparable := enc.incomparable
      encode pp msg r _ := enc.encode pp (messageEquiv p msg) r p.2 }

/-- Coordinate capture retains every returned word and encoding failure. -/
@[simp] theorem familyOfEncoding_value
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (p : OTSPosition (singleShape h w v)) (pp : PP)
    (msg : Message (singleShape h w v) M H p) (r : R) :
    (familyOfEncoding enc).value p pp msg r = enc.value pp (messageEquiv p msg) r p.2 := rfl

/-- Depth-one signatures retain their ordinary bottom data and have no upper pieces. -/
@[expose] def signatureEquiv :
    Signature R H (singleShape h w v) ≃ GXMSS.Signature R H h v where
  toFun sig := sig.bottom
  invFun sig := ⟨sig, Fin.elim0⟩
  left_inv sig := by
    rcases sig with ⟨bottom, upper⟩
    have hu : upper = Fin.elim0 := by funext i; exact i.elim0
    cases hu
    rfl
  right_inv _ := rfl

/-- Signature observation retains the original complete bottom signature. -/
theorem signatureEquiv_apply (sig : Signature R H (singleShape h w v)) :
    signatureEquiv sig = sig.bottom := rfl

/-- Remove exactly the empty internal-tape function and the unique component coordinate. -/
@[expose] def secretKeyEquiv (Coins : Type) :
    SecretKey PP H Coins (singleShape h w v) ≃ GXMSS.SecretKey PP H h v where
  toFun sk := ⟨sk.seed, fun e => sk.starts (topTree _, e), fun e => sk.endpoints (topTree _, e)⟩
  invFun sk := ⟨sk.seed, fun p => sk.starts p.2, fun p => sk.endpoints p.2, isEmptyElim⟩
  left_inv sk := by
    rcases sk with ⟨seed, starts, ends, coins⟩
    have hs : (fun p : OTSPosition (singleShape h w v) => starts (topTree _, p.2)) = starts := by
      funext p
      exact congrArg (fun t => starts (t, p.2)) (Subsingleton.elim _ _)
    have he : (fun p : OTSPosition (singleShape h w v) => ends (topTree _, p.2)) = ends := by
      funext p
      exact congrArg (fun t => ends (t, p.2)) (Subsingleton.elim _ _)
    have hc : (isEmptyElim : UpperPosition (singleShape h w v) → Coins) = coins := by
      funext p
      exact isEmptyElim p
    simp only [hs, he, hc]
  right_inv _ := rfl

/-- The raw-key map retains the common seed. -/
@[simp] theorem secretKeyEquiv_seed (sk : SecretKey PP H Coins (singleShape h w v)) :
    (secretKeyEquiv Coins sk).seed = sk.seed := rfl

/-- The actual bottom coordinate maps to the same legal ordinary epoch, without wrapping. -/
@[simp] theorem otsEquiv_bottomPosition (ep : Epoch (singleShape h w v)) :
    otsEquiv (bottomPosition (singleShape h w v) ep) = epochEquiv ep := by
  apply Fin.ext
  have hep : ep.val < 2 ^ h := by simpa [singleShape] using ep.isLt
  simp [otsEquiv, bottomPosition, positionAt, Nat.mod_eq_of_lt hep]

/-- The depth-one bottom address consists of its unique tree and unchanged epoch. -/
theorem bottomPosition_eq (ep : Epoch (singleShape h w v)) :
    bottomPosition (singleShape h w v) ep = (topTree _, epochEquiv ep) :=
  Prod.ext (tree_eq_top _) (otsEquiv_bottomPosition ep)

/-- Bottom-message interpretation followed by the fibre map preserves the application message. -/
@[simp] theorem messageEquiv_bottomMessage (ep : Epoch (singleShape h w v)) (msg : M) :
    messageEquiv (H := H) (bottomPosition (singleShape h w v) ep) (bottomMessage ep msg) = msg := by
  simp [messageEquiv, bottomMessage]

/-- All endpoints in the sole component are the ordinary endpoints. -/
theorem endpoints_eq (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (starts : OTSPosition (singleShape h w v) → Fin v → H) :
    (fun ep => endpoints (liftHash hash) pp starts (topTree _, ep)) =
      GXMSS.endpoints hash pp (fun ep => starts (topTree _, ep)) := by
  funext ep i
  simp only [endpoints, componentHash_liftHash, GXMSS.endpoints]

/-- The sole component root is the ordinary root with its existing leaf-first path convention. -/
theorem componentRoot_eq (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (ends : OTSPosition (singleShape h w v) → Fin v → H)
    (p : TreePosition (singleShape h w v)) :
    componentRoot (liftHash hash) pp ends p = hash.merkleRoot pp (fun ep => ends (p, ep)) := by
  simp only [componentRoot, componentHash_liftHash]

/-- The local authentication-path map retains the existing leaf-first ordered siblings. -/
theorem authPath_eq (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (ends : OTSPosition (singleShape h w v) → Fin v → H)
    (p : TreePosition (singleShape h w v)) (ep : Fin (2 ^ h)) :
    ((liftHash hash).componentHash p).authPath pp (fun e => ends (p, e)) ep =
      hash.authPath pp (fun e => ends (p, e)) ep := by
  rw [componentHash_liftHash]

/-- Explicit-input key assembly preserves the ordinary public key. -/
theorem keys_public_eq (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (coins : UpperPosition (singleShape h w v) → Coins) :
    (keys (liftHash hash) pp starts coins).1 =
      (GXMSS.keys hash pp (fun ep => starts (topTree _, ep))).1 := by
  simp only [keys, componentRoot_eq, endpoints_eq, GXMSS.keys]

/-- Explicit-input key assembly preserves every raw start and stored endpoint. -/
theorem keys_secret_eq (hash : GXMSS.HashInstance PP T X H h w v) (pp : PP)
    (starts : OTSPosition (singleShape h w v) → Fin v → H)
    (coins : UpperPosition (singleShape h w v) → Coins) :
    secretKeyEquiv Coins (keys (liftHash hash) pp starts coins).2 =
      (GXMSS.keys hash pp (fun ep => starts (topTree _, ep))).2 := by
  change (⟨pp, (fun ep => starts (topTree _, ep)),
    (fun ep => endpoints (liftHash hash) pp starts (topTree _, ep))⟩ :
      GXMSS.SecretKey PP H h v) = _
  rw [endpoints_eq]
  rfl

/-- Component materialization preserves the ordinary OTS prefixes and authentication path. -/
theorem componentSignature_eq (hash : GXMSS.HashInstance PP T X H h w v)
    (sk : SecretKey PP H Coins (singleShape h w v))
    (p : OTSPosition (singleShape h w v)) (wr : Codeword v (2 ^ w) × R) :
    componentSignature (liftHash hash) sk p wr =
      GXMSS.signatureOfWord hash (secretKeyEquiv Coins sk) (otsEquiv p) wr := by
  have hp : p.1 = topTree (singleShape h w v) := tree_eq_top p.1
  simp only [componentSignature, componentHash_liftHash]
  cases p with
  | mk tree leaf =>
    dsimp only at hp
    cases hp
    rfl

/-- At depth one, optional signing materializes exactly the successful bottom retry result.
There are no internal results whose failure could suppress a successful bottom word. -/
theorem signWithCoins_single (hash : HashInstance PP T X H (singleShape h w v))
    (family : EncodingFamily PP M R H (singleShape h w v)) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins (singleShape h w v))
    (ep : Epoch (singleShape h w v)) (msg : M) (coins : sampling.bottom.Coins) :
    (signWithCoins hash family sampling sk ep msg coins).map signatureEquiv =
      (componentResult family sampling.bottom sk (bottomPosition _ ep) (bottomMessage ep msg)
        coins).output.map (componentSignature hash sk (bottomPosition _ ep)) := by
  unfold signWithCoins
  cases (componentResult family sampling.bottom sk (bottomPosition _ ep) (bottomMessage ep msg)
    coins).output <;> rfl

/-- The single layer's verifier agrees on every signature, including failed re-encodings. -/
theorem verify_eq [DecidableEq H] (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (pk : GXMSS.PublicKey PP H) (ep : Epoch (singleShape h w v)) (msg : M)
    (sig : Signature R H (singleShape h w v)) :
    verify (liftHash hash) (familyOfEncoding enc) pk ep msg sig =
      GXMSS.verify hash enc pk (epochEquiv ep) msg (signatureEquiv sig) := by
  simp only [verify, recoverRoot, singleShape, Nat.sub_self, recoverThrough,
    recoverComponent, familyOfEncoding_value, messageEquiv_bottomMessage,
    componentHash_liftHash]
  have he : (bottomPosition (singleShape h w v) ep).2 = epochEquiv ep :=
    otsEquiv_bottomPosition ep
  rw [he]
  cases hv : enc.value pk.seed msg sig.bottom.randomizer (epochEquiv ep)
  · simp [GXMSS.verify, signatureEquiv, hv]
  · simp [GXMSS.verify, signatureEquiv, hv]
    rfl

/-- Fixed IID tapes produce the same full retry result at the ordinary epoch. -/
theorem componentResult_iid_eq [SampleableType R]
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : SecretKey PP H Coins (singleShape h w v))
    (ep : Epoch (singleShape h w v)) (msg : M) (coins : (RetryPlan.iid R K).Coins) :
    componentResult (familyOfEncoding enc) (RetryPlan.iid R K) sk
      (bottomPosition (singleShape h w v) ep) (bottomMessage ep msg) coins =
      (RetryPlan.iid R K).run enc sk.seed msg (epochEquiv ep) coins := by
  apply RetryPlan.run_eq_of_values_eq
  intro i
  simp only [Encoding.Family.value_atEpoch, familyOfEncoding_value,
    messageEquiv_bottomMessage]
  exact congrArg (enc.value sk.seed msg ((RetryPlan.iid R K).randomizers coins i))
    (otsEquiv_bottomPosition ep)

/-- Forgetting the empty upper array preserves each optional fixed-tape signing result. -/
theorem signWithCoins_iid_eq [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (sk : SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v))
    (ep : Epoch (singleShape h w v)) (msg : M) (coins : (RetryPlan.iid R K).Coins) :
    (signWithCoins (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
      sk ep msg coins).map signatureEquiv =
      ((RetryPlan.iid R K).run enc sk.seed msg (epochEquiv ep) coins).output.map
        (GXMSS.signatureOfWord hash (secretKeyEquiv _ sk) (epochEquiv ep)) := by
  dsimp only [RetrySampling.iid] at sk ⊢
  simp only [signWithCoins]
  rw [componentResult_iid_eq]
  cases ((RetryPlan.iid R K).run enc sk.seed msg (epochEquiv ep) coins).output with
  | none => rfl
  | some wr =>
    change some (componentSignature (liftHash hash) sk
      (bottomPosition (singleShape h w v) ep) wr) = _
    rw [componentSignature_eq, otsEquiv_bottomPosition]
    rfl

/-- Actual IID signing transports the returned optional signature, preserving exhaustion. -/
theorem sign_iid_evalDistEq [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (sk : SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v))
    (ep : Epoch (singleShape h w v)) (msg : M) :
    Option.map signatureEquiv <$>
      sign (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) sk ep msg =ᵈ
        GXMSS.sign hash enc K (secretKeyEquiv _ sk) (epochEquiv ep) msg := by
  have he := signWithCoins_iid_eq hash enc K J sk ep msg
  dsimp only [RetrySampling.iid] at sk he ⊢
  have hd := (RetryPlan.iid_run_output_evalDistEq_retry enc sk.seed msg (epochEquiv ep) K).map
    (Option.map (GXMSS.signatureOfWord hash (secretKeyEquiv _ sk) (epochEquiv ep)))
  simp only [sign, Functor.map_map]
  simp only [he]
  change _ =ᵈ Option.map (GXMSS.signatureOfWord hash (secretKeyEquiv _ sk) (epochEquiv ep))
    <$> enc.retry ($ᵗ R) sk.seed msg (epochEquiv ep) K
  intro event
  have hh := hd event
  simp only [prEvent_map] at hh ⊢
  dsimp [secretKeyEquiv] at hh ⊢
  exact hh

/-- Reindex the unique component's complete start table by ordinary epochs. -/
@[expose] def startsEquiv :
    (OTSPosition (singleShape h w v) → Fin v → H) ≃ (Fin (2 ^ h) → Fin v → H) :=
  Equiv.arrowCongr otsEquiv (Equiv.refl _)

/-- Start-table reindexing reads exactly the same chain label. -/
@[simp] theorem startsEquiv_apply
    (starts : OTSPosition (singleShape h w v) → Fin v → H) (ep : Fin (2 ^ h)) :
    startsEquiv starts ep = starts (topTree _, ep) := rfl

/-- The observed raw secret key retains exactly the reindexed starts. -/
@[simp] theorem secretKeyEquiv_starts (sk : SecretKey PP H Coins (singleShape h w v)) :
    (secretKeyEquiv Coins sk).starts = startsEquiv sk.starts := rfl

/-- The observed raw secret key retains exactly the reindexed stored endpoints. -/
@[simp] theorem secretKeyEquiv_endpoints (sk : SecretKey PP H Coins (singleShape h w v)) :
    (secretKeyEquiv Coins sk).endpoints = startsEquiv sk.endpoints := rfl

/-- Forest start sampling transports to the old independent finite-array sampler. -/
theorem sampleStarts_evalDistEq [SampleableType H] :
    startsEquiv <$> sampleStarts (H := H) (singleShape h w v) =ᵈ
      GXMSS.sampleStarts H h v := by
  let : Fintype (OTSPosition (singleShape h w v)) := Fintype.ofFinite _
  let : MeasurableSpace H := ⊤
  have hi : 𝒟[Fin.mOfFn v (fun _ => ($ᵗ H : ProbComp H))] =
      uniformOn Set.univ :=
    evalDist_mOfFn_const_uniform v ($ᵗ H) SampleableType.evalDist_uniformSample
  apply EvalDistEq.of_evalDist_eq
  rw [evalDist_map_of_discrete]
  change (𝒟[Fintype.mPi (fun _ : OTSPosition (singleShape h w v) =>
    Fin.mOfFn v (fun _ => ($ᵗ H : ProbComp H)))]).map startsEquiv =
      𝒟[Fin.mOfFn (2 ^ h) (fun _ => Fin.mOfFn v (fun _ => ($ᵗ H : ProbComp H)))]
  rw [evalDist_mPi_const_uniform _ hi, evalDist_mOfFn_const_uniform _ _ hi]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete startsEquiv.bijective

/-- With no upper positions, every internal-tape sampler has its unique returned value. -/
theorem sampleUpperCoins_evalDistEq (sample : ProbComp Coins) :
    sampleUpperCoins (singleShape h w v) sample =ᵈ
      (pure (isEmptyElim : UpperPosition (singleShape h w v) → Coins) : ProbComp _) := by
  classical
  intro event
  have he : event = fun _ => event (isEmptyElim : UpperPosition (singleShape h w v) → Coins) := by
    funext coins
    congr 1
    funext p
    exact isEmptyElim p
  rw [he]
  by_cases hp : event (isEmptyElim : UpperPosition (singleShape h w v) → Coins)
  · rw [prEvent_const_of_lossless _ (by simp) hp, prEvent_pure]
    simp only [hp, ite_true]
  · rw [prEvent_const_of_not _ hp, prEvent_pure]
    simp only [hp, ite_false]

/-- Key-generation observation removes only the unique component coordinate and empty tapes. -/
@[expose] def keyObservation (Coins : Type)
    (pair : GXMSS.PublicKey PP H × SecretKey PP H Coins (singleShape h w v)) :
    GXMSS.PublicKey PP H × GXMSS.SecretKey PP H h v :=
  (pair.1, secretKeyEquiv Coins pair.2)

/-- Actual key generation has the old returned-key law after the explicit raw-key map. -/
theorem keygen_evalDistEq [SampleableType H] (hash : GXMSS.HashInstance PP T X H h w v)
    (sampling : RetrySampling R) :
    keyObservation sampling.internal.Coins <$> keygen (liftHash hash) sampling =ᵈ
      GXMSS.keygen hash := by
  simp only [keygen, GXMSS.keygen, map_bind]
  apply EvalDistEq.bind_right
  intro pp
  have hs := sampleStarts_evalDistEq (H := H) (h := h) (w := w) (v := v)
  have ht := hs.bind_left (fun starts => pure (GXMSS.keys hash pp starts))
  simp only [bind_map_left] at ht
  apply EvalDistEq.trans _ ht
  apply EvalDistEq.bind_right
  intro starts
  have hu := (sampleUpperCoins_evalDistEq (h := h) (w := w) (v := v)
    sampling.sampleInternal).map (fun coins => keyObservation sampling.internal.Coins
      (keys (liftHash hash) pp starts coins))
  simp only [map_pure]
  have hm : (do
      let coins ← sampleUpperCoins (singleShape h w v) sampling.sampleInternal
      pure (keyObservation sampling.internal.Coins (keys (liftHash hash) pp starts coins))) =
      (fun coins => keyObservation sampling.internal.Coins
        (keys (liftHash hash) pp starts coins)) <$>
          sampleUpperCoins (singleShape h w v) sampling.sampleInternal := by
    simp only [map_eq_bind_pure_comp, Function.comp_def]
  rw [hm]
  change ((fun coins => keyObservation sampling.internal.Coins
    (keys (liftHash hash) pp starts coins)) <$> sampleUpperCoins _ sampling.sampleInternal :
      ProbComp (GXMSS.PublicKey PP H × GXMSS.SecretKey PP H h v)) =ᵈ
        (pure (GXMSS.keys hash pp (startsEquiv starts)) : ProbComp _)
  have ho : (fun coins : UpperPosition (singleShape h w v) → sampling.internal.Coins =>
      keyObservation sampling.internal.Coins
      (keys (liftHash hash) pp starts coins)) =
      fun _ : UpperPosition (singleShape h w v) → sampling.internal.Coins =>
        GXMSS.keys hash pp (startsEquiv starts) := by
    funext coins
    exact Prod.ext (keys_public_eq hash pp starts coins) (keys_secret_eq hash pp starts coins)
  rw [ho] at hu ⊢
  simpa only [map_pure] using hu

end GXMSS.Hypertree.SingleLayer
