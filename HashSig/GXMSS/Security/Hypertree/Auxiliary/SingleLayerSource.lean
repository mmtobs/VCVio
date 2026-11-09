/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.SingleLayer
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
public import VCVio.OracleComp.SimSemantics.StateT.Measure
import all HashSig.GXMSS.Hypertree.SingleLayer
import all HashSig.GXMSS.Hypertree.Scheme
import all VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.EvalDist.EvalDistEq
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
import all HashSig.GXMSS.Scheme

/-!
# Single-layer native source observations

Depth-one forest interfaces are reindexed explicitly. IID retry transport preserves optional
answers before lifting through the adaptive synchronized handler; duplicate and failed requests
therefore retain their first-request history.
-/

public section

namespace GXMSS.Hypertree.SingleLayer

open Encoding OracleComp OracleSpec SyncSignatureUnforgeability

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Observe a depth-one forgery in the ordinary epoch and signature domains. -/
@[expose] def forgeryObservation
    (forgery : Forgery (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) :
    Forgery (Fin (2 ^ h)) M (GXMSS.Signature R H h v) :=
  (epochEquiv forgery.1, forgery.2.1, signatureEquiv forgery.2.2)

/-- Observe every consumed epoch, retaining returned signing failures. -/
@[expose] def historyObservation
    (history : History (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) :
    History (Fin (2 ^ h)) M (GXMSS.Signature R H h v) :=
  fun ep => (history (epochEquiv.symm ep)).map fun entry =>
    (entry.1, entry.2.map signatureEquiv)

/-- The public source observation discards only private retry metadata and reindexes domains. -/
@[expose] def resultObservation {Coins : Type}
    (out : Security.Result PP H M R Coins (singleShape h w v)) :
    ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M (GXMSS.Signature R H h v) :=
  (out.pk, forgeryObservation out.forgery, historyObservation out.history)

/-- Reindexing first-request history preserves the exact successful message/signature pair. -/
theorem strongFresh_observation [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    [DecidableEq (Signature R H (singleShape h w v))]
    (history : History (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v)))
    (forgery : Forgery (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) :
    strongFresh (historyObservation history) (forgeryObservation forgery) =
      strongFresh history forgery := by
  rcases forgery with ⟨ep, msg, sig⟩
  cases hh : history ep with
  | none => simp [strongFresh, historyObservation, forgeryObservation, hh]
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none => simp [strongFresh, historyObservation, forgeryObservation, hh]
    | some honest =>
      simp only [strongFresh, historyObservation, forgeryObservation,
        Equiv.symm_apply_apply, hh, Option.map_some]
      apply decide_eq_decide.mpr
      simp [signatureEquiv.injective.eq_iff]

/-- Reindexing preserves ordinary message freshness, including explicit signing failure. -/
theorem fresh_observation [DecidableEq M]
    (history : History (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v)))
    (forgery : Forgery (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) :
    fresh (historyObservation history) (forgeryObservation forgery) = fresh history forgery := by
  rcases forgery with ⟨ep, msg, sig⟩
  cases hh : history ep with
  | none => simp [fresh, historyObservation, forgeryObservation, hh]
  | some entry =>
      simp only [fresh, historyObservation, forgeryObservation, Equiv.symm_apply_apply,
        hh, Option.map_some]
      by_cases he : msg = entry.1 <;> simp [he]

/-- Ordinary signing lifted back to the depth-one public response representation. -/
theorem sign_iid_lift_evalDistEq [SampleableType R]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (sk : SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v)) (ep : Epoch (singleShape h w v)) (msg : M) :
    sign (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J) sk ep msg =ᵈ
      Option.map signatureEquiv.symm <$>
        GXMSS.sign hash enc K (secretKeyEquiv _ sk) (epochEquiv ep) msg := by
  have hd := (sign_iid_evalDistEq hash enc K J sk ep msg).map
    (Option.map (signatureEquiv (w := w)).symm)
  simp only [Functor.map_map] at hd
  have back : (fun answer : Option (Signature R H (singleShape h w v)) =>
      Option.map (signatureEquiv (w := w)).symm
        (Option.map (signatureEquiv (w := w)) answer)) = id := by
    funext answer
    cases answer <;> simp
  rw [back, id_map] at hd
  exact hd


/-- The old signer and verifier expressed in the depth-one coordinate domains.
The generated raw forest key is observed by `keygen_evalDistEq`. -/
@[expose] noncomputable def ordinaryOnGlobal [SampleableType H] [SampleableType R]
    [DecidableEq H] (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ) :
    SyncSignatureAlg ProbComp M (GXMSS.PublicKey PP H)
      (SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins (singleShape h w v))
      (Signature R H (singleShape h w v)) (Epoch (singleShape h w v)) where
  keygen := keygen (liftHash hash) (RetrySampling.iid K J)
  sign sk ep msg := Option.map signatureEquiv.symm <$>
    GXMSS.sign hash enc K (secretKeyEquiv _ sk) (epochEquiv ep) msg
  verify pk ep msg sig := GXMSS.verify hash enc pk (epochEquiv ep) msg (signatureEquiv sig)

/-- Every synchronized query retains the same joint response and first-request history. -/
theorem signingOracle_iid_evalDistEq [SampleableType H] [SampleableType R]
    [DecidableEq H] (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (sk : SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v))
    (q : Epoch (singleShape h w v) × M)
    (history : History (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) :
    signingOracle (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)) sk q
      history =ᵈ signingOracle (ordinaryOnGlobal hash enc K J) sk q history := by
  rcases q with ⟨ep, msg⟩
  cases hh : history ep with
  | some entry => simp only [signingOracle, hh]; rfl
  | none =>
    simp only [signingOracle, hh, scheme, ordinaryOnGlobal]
    exact (sign_iid_lift_evalDistEq hash enc K J sk ep msg).bind_left
      (fun answer => pure (answer, Function.update history ep (some (msg, answer))))

/-- The entire native interaction has the ordinary signer law under the global interface.
This is an adaptive returned-output law, including failures and consumed epochs. -/
theorem interaction_iid_evalDistEq [SampleableType H] [SampleableType R]
    [DecidableEq H] (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    interaction (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)) adv =ᵈ
      interaction (ordinaryOnGlobal hash enc K J) adv := by
  unfold interaction
  apply EvalDistEq.bind_right
  intro pair
  apply EvalDistEq.bind_left
  apply evalDistEq_simulateQ_run
  intro q history
  cases q with
  | inl q => rfl
  | inr q => exact signingOracle_iid_evalDistEq hash enc K J pair.2 q history

/-- The enriched observation retains the raw ordinary secret key as well as the complete history. -/
@[expose] def enrichedSourceObservation {Coins : Type}
    (out : Security.Result PP H M R Coins (singleShape h w v)) :
    GXMSS.Reductions.Result PP H M R h v :=
  ⟨out.pk, secretKeyEquiv Coins out.sk, forgeryObservation out.forgery,
    historyObservation out.history⟩

/-- Translate actual global signing queries to ordinary epochs and lift optional answers back. -/
@[expose] def queryBridge : QueryImpl
    (unifSpec + signingSpec (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v)))
    (OracleComp (unifSpec + signingSpec (Fin (2 ^ h)) M (GXMSS.Signature R H h v)))
  | .inl q => liftM ((unifSpec + signingSpec (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)).query (Sum.inl q))
  | .inr (ep, msg) => Option.map signatureEquiv.symm <$>
      liftM ((unifSpec + signingSpec (Fin (2 ^ h)) M
        (GXMSS.Signature R H h v)).query (Sum.inr (epochEquiv ep, msg)))

/-- The same adaptive adversary expressed over ordinary signing queries and returned data. -/
@[expose] def adversaryToOrdinary
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    GXMSS.Reductions.SchemeAdversary PP H M R h v where
  forge pk := forgeryObservation <$> simulateQ queryBridge (adv.forge pk)

/-- History reindexing commutes with the first-request update, including a failed answer. -/
theorem historyObservation_update
    (history : History (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v)))
    (ep : Epoch (singleShape h w v)) (msg : M)
    (answer : Option (Signature R H (singleShape h w v))) :
    historyObservation (Function.update history ep (some (msg, answer))) =
      Function.update (historyObservation history) (epochEquiv ep)
        (some (msg, answer.map signatureEquiv)) := by
  funext other
  by_cases he : epochEquiv.symm other = ep
  · have ho : other = epochEquiv ep := (Equiv.symm_apply_eq _).mp he
    subst other
    simp [historyObservation, Function.update]
  · have ho : other ≠ epochEquiv ep := by
      intro ho
      exact he (by simp [ho])
    simp [historyObservation, Function.update, he, ho]

private def ordinaryOracles [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) : QueryImpl
    (unifSpec + signingSpec (Fin (2 ^ h)) M (GXMSS.Signature R H h v))
    (StateT (History (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (History (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) ProbComp) +
      signingOracle (GXMSS.scheme hash enc K) sk

private noncomputable def liftedOracles [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (sk : SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v)) : QueryImpl
    (unifSpec + signingSpec (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v)))
    (StateT (History (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v)))
      ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (History (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v)))
      ProbComp) + signingOracle (ordinaryOnGlobal hash enc K J) sk

private theorem liftedOracles_projection [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (sk : SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v))
    (q : (unifSpec + signingSpec (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))).Domain)
    (history : History (Epoch (singleShape h w v)) M (Signature R H (singleShape h w v))) :
    Prod.map id historyObservation <$> (liftedOracles hash enc K J sk q).run history =
      (simulateQ (ordinaryOracles hash enc K (secretKeyEquiv _ sk))
        (queryBridge q)).run (historyObservation history) := by
  cases q with
  | inl uniform =>
      simp [liftedOracles, ordinaryOracles, queryBridge]
  | inr request =>
      rcases request with ⟨ep, msg⟩
      simp only [liftedOracles, ordinaryOracles, queryBridge, QueryImpl.add_apply_inr,
        simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_map]
      change Prod.map id historyObservation <$>
        signingOracle (ordinaryOnGlobal hash enc K J) sk (ep, msg) history =
          (fun p => (Option.map signatureEquiv.symm p.1, p.2)) <$>
            signingOracle (GXMSS.scheme hash enc K) (secretKeyEquiv _ sk)
              (epochEquiv ep, msg) (historyObservation history)
      cases hh : history ep with
      | some entry =>
          rcases entry with ⟨first, answer⟩
          have ho : historyObservation history (epochEquiv ep) =
              some (first, answer.map signatureEquiv) := by
            simp [historyObservation, hh]
          rw [signingOracle_used _ _ _ _ _ _ _ hh,
            signingOracle_used _ _ _ _ _ _ _ ho]
          simp
      | none =>
          have ho : historyObservation history (epochEquiv ep) = none := by
            simp [historyObservation, hh]
          rw [signingOracle_unused _ _ _ _ _ hh,
            signingOracle_unused _ _ _ _ _ ho]
          change Prod.map id historyObservation <$>
            ((Option.map signatureEquiv.symm <$>
              GXMSS.sign hash enc K (secretKeyEquiv _ sk) (epochEquiv ep) msg) >>=
              fun answer => pure (answer, Function.update history ep (some (msg, answer)))) = _
          simp only [map_bind, bind_map_left, map_pure]
          apply congrArg (fun next => GXMSS.sign hash enc K (secretKeyEquiv _ sk)
            (epochEquiv ep) msg >>= next)
          funext answer
          simp only [Prod.map, Function.id_def, historyObservation_update]
          cases answer <;> simp


private theorem fixed_run_iid_evalDistEq [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (pk : GXMSS.PublicKey PP H)
    (sk : SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v)) :
    (fun result => (forgeryObservation result.1, historyObservation result.2.1)) <$>
      (simulateQ (Security.nativeOracles (liftHash hash) (familyOfEncoding enc)
        (RetrySampling.iid K J) sk) (adv.forge pk)).run (emptyHistory, []) =ᵈ
      (simulateQ (ordinaryOracles hash enc K (secretKeyEquiv _ sk))
        ((adversaryToOrdinary adv).forge pk)).run emptyHistory := by
  have hn := Security.native_run_proj (liftHash hash) (familyOfEncoding enc)
    (RetrySampling.iid K J) sk (adv.forge pk) (emptyHistory, [])
  have hi : (simulateQ (Security.sourceOracles (liftHash hash) (familyOfEncoding enc)
      (RetrySampling.iid K J) sk) (adv.forge pk)).run emptyHistory =ᵈ
        (simulateQ (liftedOracles hash enc K J sk) (adv.forge pk)).run emptyHistory := by
    apply evalDistEq_simulateQ_run
    intro q history
    cases q with
    | inl q => rfl
    | inr q => exact signingOracle_iid_evalDistEq hash enc K J sk q history
  have hp := map_run_simulateQ_eq_of_query_map_eq
    (liftedOracles hash enc K J sk)
    (ordinaryOracles hash enc K (secretKeyEquiv _ sk) ∘ₛ queryBridge)
    historyObservation (liftedOracles_projection hash enc K J sk) (adv.forge pk) emptyHistory
  have hs := hi.map (fun result => (forgeryObservation result.1, historyObservation result.2))
  rw [← hn] at hs
  simp only [Functor.map_map, Prod.map, Function.id_def] at hs
  apply hs.trans
  have hpm := congrArg (fun program =>
    (fun result => (forgeryObservation result.1, result.2)) <$> program) hp
  simp only [Functor.map_map, Prod.map, Function.id_def, QueryImpl.simulateQ_compose] at hpm
  rw [hpm]
  simp only [adversaryToOrdinary, simulateQ_map, StateT.run_map]
  exact EvalDistEq.refl _

/-- Fixed-key native IID signing transports to the actual ordinary enriched source run. -/
theorem runWithKeys_iid_evalDistEq [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v))
    (pk : GXMSS.PublicKey PP H)
    (sk : SecretKey PP H (RetrySampling.iid (R := R) K J).internal.Coins
      (singleShape h w v)) :
    enrichedSourceObservation <$>
      Security.runWithKeys (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
        adv pk sk =ᵈ GXMSS.Reductions.runWithKeys hash enc K (adversaryToOrdinary adv)
          pk (secretKeyEquiv _ sk) := by
  have hrun := (fixed_run_iid_evalDistEq hash enc K J adv pk sk).map
    (fun result => (⟨pk, secretKeyEquiv _ sk, result.1, result.2⟩ :
      GXMSS.Reductions.Result PP H M R h v))
  simpa only [Security.runWithKeys, GXMSS.Reductions.runWithKeys,
    enrichedSourceObservation, ordinaryOracles, Functor.map_map,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hrun

/-- Actual native IID source sampling transports through the explicit raw-key observation.
No conditional law or surrogate source computation is used. -/
theorem sourceProgram_iid_evalDistEq [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    enrichedSourceObservation <$>
      Security.sourceProgram (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)
        adv =ᵈ GXMSS.Reductions.sourceProgram hash enc K (adversaryToOrdinary adv) := by
  unfold Security.sourceProgram GXMSS.Reductions.sourceProgram
  rw [map_bind]
  calc
    _ =ᵈ keygen (liftHash hash) (RetrySampling.iid K J) >>= fun keys =>
        GXMSS.Reductions.runWithKeys hash enc K (adversaryToOrdinary adv)
          keys.1 (secretKeyEquiv _ keys.2) :=
      EvalDistEq.bind_right _ (fun keys => runWithKeys_iid_evalDistEq hash enc K J adv
        keys.1 keys.2)
    _ =ᵈ _ := by
      have hk := (keygen_evalDistEq hash (RetrySampling.iid (R := R) K J)).bind_left
        (fun keys => GXMSS.Reductions.runWithKeys hash enc K (adversaryToOrdinary adv)
          keys.1 keys.2)
      simpa only [bind_map_left, keyObservation] using hk


/-- Reindex the complete public interaction result without changing its Boolean observations. -/
@[expose] def interactionObservation
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))) :
    ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M (GXMSS.Signature R H h v) :=
  (out.1, forgeryObservation out.2.1, historyObservation out.2.2)

/-- The full IID interaction has the ordinary interaction law after explicit domain reindexing. -/
theorem interaction_iid_reindex_evalDistEq [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    interactionObservation <$>
      interaction (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)) adv =ᵈ
        interaction (GXMSS.scheme hash enc K) (adversaryToOrdinary adv) := by
  have hs := (sourceProgram_iid_evalDistEq hash enc K J adv).map
    GXMSS.Reductions.sourceObservation
  rw [GXMSS.Reductions.sourceProgram_map_eq_interaction] at hs
  rw [← Security.sourceProgram_map_eq_interaction]
  simpa only [Functor.map_map, enrichedSourceObservation, interactionObservation,
    Security.sourceObservation, GXMSS.Reductions.sourceObservation] using hs

/-- Strong-pair validity agrees on every observed result, including arbitrary invalid signatures. -/
theorem strongValid_observation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    [DecidableEq (Signature R H (singleShape h w v))]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))) :
    strongValid (GXMSS.scheme hash enc K) (interactionObservation out) =
      strongValid (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)) out := by
  change (GXMSS.verify hash enc out.1 (epochEquiv out.2.1.1) out.2.1.2.1
    (signatureEquiv out.2.1.2.2) && strongFresh (historyObservation out.2.2)
      (forgeryObservation out.2.1)) = _
  rw [strongFresh_observation, ← verify_eq hash enc]
  rfl

/-- Ordinary-message validity agrees on the full reindexed result. -/
theorem valid_observation [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch (singleShape h w v)) M
      (Signature R H (singleShape h w v))) :
    valid (GXMSS.scheme hash enc K) (interactionObservation out) =
      valid (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J)) out := by
  change (GXMSS.verify hash enc out.1 (epochEquiv out.2.1.1) out.2.1.2.1
    (signatureEquiv out.2.1.2.2) && fresh (historyObservation out.2.2)
      (forgeryObservation out.2.1)) = _
  rw [fresh_observation, ← verify_eq hash enc]
  rfl

/-- The complete strong Boolean game measure specializes exactly to the ordinary game. -/
theorem strongUnforgeableExp_iid_eq [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    [DecidableEq (Signature R H (singleShape h w v))]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    strongUnforgeableExp
      (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J))
      ProbCompRuntime.probComp adv =
        strongUnforgeableExp (GXMSS.scheme hash enc K) ProbCompRuntime.probComp
          (adversaryToOrdinary adv) := by
  have hs := (interaction_iid_reindex_evalDistEq hash enc K J adv).map
    (strongValid (GXMSS.scheme hash enc K))
  simp only [Functor.map_map, strongValid_observation hash enc K J] at hs
  simpa only [strongUnforgeableExp, outputMeasure, ProbCompRuntime.probComp_evalDist]
    using hs.evalDist_eq

/-- The complete regular Boolean game measure specializes exactly to the ordinary game. -/
theorem unforgeableExp_iid_eq [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    unforgeableExp (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J))
      ProbCompRuntime.probComp adv =
        unforgeableExp (GXMSS.scheme hash enc K) ProbCompRuntime.probComp
          (adversaryToOrdinary adv) := by
  have hs := (interaction_iid_reindex_evalDistEq hash enc K J adv).map
    (valid (GXMSS.scheme hash enc K))
  simp only [Functor.map_map, valid_observation hash enc K J] at hs
  simpa only [unforgeableExp, outputMeasure, ProbCompRuntime.probComp_evalDist]
    using hs.evalDist_eq

/-- Strong advantage is preserved, including the native mass of returned failure. -/
theorem strongAdvantage_iid_eq [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    [DecidableEq (Signature R H (singleShape h w v))]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    strongAdvantage (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J))
      ProbCompRuntime.probComp adv =
        strongAdvantage (GXMSS.scheme hash enc K) ProbCompRuntime.probComp
          (adversaryToOrdinary adv) := by
  unfold strongAdvantage
  rw [strongUnforgeableExp_iid_eq hash enc K J adv]

/-- Ordinary advantage is preserved by the same actual adaptive adversary translation. -/
theorem advantage_iid_eq [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    (hash : GXMSS.HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K J : ℕ)
    (adv : Security.SchemeAdversary PP H M R (singleShape h w v)) :
    advantage (scheme (liftHash hash) (familyOfEncoding enc) (RetrySampling.iid K J))
      ProbCompRuntime.probComp adv =
        advantage (GXMSS.scheme hash enc K) ProbCompRuntime.probComp
          (adversaryToOrdinary adv) := by
  unfold advantage
  rw [unforgeableExp_iid_eq hash enc K J adv]

/-- Every consumed history entry has its actual native bottom-attempt record. -/
@[expose] def HistoryHasAttempt {S : Shape} (state : Security.NativeState M H R S) : Prop :=
  ∀ ep msg answer, state.1 ep = some (msg, answer) →
    ∃ entry ∈ state.2, entry.epoch = ep ∧ entry.message = msg

private theorem signingOracleWithAttempts_preserves_historyHasAttempt {S : Shape} {Coins : Type}
    (sample : ProbComp Coins)
    (attempt : Epoch S → M → Coins → IncomparableEncoding.IndexedResult R S.v (2 ^ S.w))
    (signer : Epoch S → M → Coins → Option (Signature R H S))
    (q : Epoch S × M) (state : Security.NativeState M H R S)
    (hinv : HistoryHasAttempt state)
    (out : Option (Signature R H S) × Security.NativeState M H R S)
    (hout : out ∈ support
      ((Security.signingOracleWithAttempts sample attempt signer q).run state)) :
    HistoryHasAttempt out.2 := by
  rcases q with ⟨ep, msg⟩
  change out ∈ support (Security.signingOracleWithAttempts sample attempt signer (ep, msg)
    state) at hout
  cases hu : state.1 ep with
  | some first =>
      simp only [Security.signingOracleWithAttempts, hu, support_pure,
        Set.mem_singleton_iff] at hout
      subst out
      exact hinv
  | none =>
      simp only [Security.signingOracleWithAttempts, hu, mem_support_bind_iff] at hout
      obtain ⟨coins, _, hret⟩ := hout
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst out
      intro other message answer hrecord
      by_cases he : other = ep
      · subst other
        have hm : msg = message := by
          have hp : (msg, signer ep msg coins) = (message, answer) := by
            simpa [Function.update] using hrecord
          exact congrArg Prod.fst hp
        refine ⟨⟨ep, msg, attempt ep msg coins⟩, ?_, rfl, hm⟩
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · obtain ⟨entry, hentry, hepoch, hmessage⟩ := hinv other message answer
          (by simpa [Function.update, he] using hrecord)
        exact ⟨entry, List.mem_append_left _ hentry, hepoch, hmessage⟩

/-- All native first-request records, successful or failed, have logged attempts. -/
theorem runWithKeys_history_has_attempt {S : Shape}
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S)
    (out : Security.Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (Security.runWithKeys hash family sampling adv pk sk))
    (ep : Epoch S) (msg : M) (answer : Option (Signature R H S))
    (hrecord : out.history ep = some (msg, answer)) :
    ∃ entry ∈ out.bottomAttempts, entry.epoch = ep ∧ entry.message = msg := by
  have hpres : QueryImpl.PreservesInv (Security.nativeOracles hash family sampling sk)
      HistoryHasAttempt := by
    intro q state hinv result hresult
    cases q with
    | inl uniform =>
        simp only [Security.nativeOracles, QueryImpl.add_apply_inl,
          QueryImpl.liftTarget_apply] at hresult
        change result ∈ support ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)
          uniform) >>= fun answer => pure (answer, state)) at hresult
        simp only [mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hret⟩ := hresult
        simp only [support_pure, Set.mem_singleton_iff] at hret
        subst result
        exact hinv
    | inr request =>
        simp only [Security.nativeOracles, QueryImpl.add_apply_inr,
          Security.nativeSigningOracle] at hresult
        exact signingOracleWithAttempts_preserves_historyHasAttempt sampling.sampleBottom
          (fun ep msg coins => componentResult family sampling.bottom sk (bottomPosition S ep)
            (bottomMessage ep msg) coins) (signWithCoins hash family sampling sk)
          request state hinv result hresult
  have hinit : HistoryHasAttempt
      ((emptyHistory, []) : Security.NativeState M H R S) := by
    intro ep msg answer hentry
    simp [emptyHistory] at hentry
  simp only [Security.runWithKeys, mem_support_bind_iff] at hout
  obtain ⟨result, hresult, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  exact (simulateQ_run_preservesInv (Security.nativeOracles hash family sampling sk)
    HistoryHasAttempt hpres (adv.forge pk) (emptyHistory, []) hinit result hresult)
      ep msg answer hrecord

/-- The actual source program has no consumed history entry missing its native attempt. -/
theorem sourceProgram_history_has_attempt {S : Shape} [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (out : Security.Result PP H M R sampling.internal.Coins S)
    (hout : out ∈ support (Security.sourceProgram hash family sampling adv))
    (ep : Epoch S) (msg : M) (answer : Option (Signature R H S))
    (hrecord : out.history ep = some (msg, answer)) :
    ∃ entry ∈ out.bottomAttempts, entry.epoch = ep ∧ entry.message = msg := by
  simp only [Security.sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨keys, _, hrun⟩ := hout
  exact runWithKeys_history_has_attempt hash family sampling adv keys.1 keys.2 out hrun
    ep msg answer hrecord


end GXMSS.Hypertree.SingleLayer
