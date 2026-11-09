/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Scheme
public import VCVio.CryptoFoundations.SyncSignatureCorrectness
import all HashSig.GXMSS.Scheme

/-!
# Successful-output correctness of generalized XMSS hypertrees

Component chain completion and ordered Merkle recovery compose through every layer. Fixed
internal retry exhaustion is preserved; successful-output correctness does not assert that
every generated key has small signing failure probability.
-/

public section

namespace GXMSS.Hypertree

open Encoding ENNReal OracleComp

variable {PP T X H M R Coins : Type} {S : Shape}

/-- Stored endpoints and the public top root agree with the actual full forest. -/
@[expose] def Consistent (hash : HashInstance PP T X H S)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H Coins S) : Prop :=
  pk.seed = sk.seed ∧ sk.endpoints = endpoints hash sk.seed sk.starts ∧
    pk.root = componentRoot hash sk.seed sk.endpoints (topTree S)

/-- Explicit-input key assembly always produces a consistent forest. -/
theorem consistent_keys (hash : HashInstance PP T X H S) (pp : PP)
    (starts : OTSPosition S → Fin S.v → H) (coins : UpperPosition S → Coins) :
    Consistent hash (keys hash pp starts coins).1 (keys hash pp starts coins).2 := by
  simp [Consistent, keys]

/-- A valid word and honest component signature recover the component's actual root. -/
theorem recoverComponent_componentSignature (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sk : SecretKey PP H Coins S)
    (hend : sk.endpoints = endpoints hash sk.seed sk.starts)
    (p : OTSPosition S) (msg : Message S M H p) (wr : Codeword S.v (2 ^ S.w) × R)
    (hword : family.value p sk.seed msg wr.2 = some wr.1) :
    recoverComponent hash family sk.seed p msg (componentSignature hash sk p wr) =
      some (componentRoot hash sk.seed sk.endpoints p.1) := by
  have hchains : (fun i => (hash.componentHash p.1).chain sk.seed p.2 i (wr.1 i)
      (2 ^ S.w - 1 - (wr.1 i).val)
      ((hash.componentHash p.1).chain sk.seed p.2 i 0 (wr.1 i) (sk.starts p i))) =
      sk.endpoints p := by
    funext i
    rw [GXMSS.HashInstance.chain_complete_digit, hend]
    rfl
  simp only [recoverComponent, componentSignature, GXMSS.signatureOfWord,
    componentSecretKey, hword, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [hchains]
  exact congrArg some ((hash.componentHash p.1).recoverRoot_authPath sk.seed
    (fun ep => sk.endpoints (p.1, ep)) p.2)

/-- A successful fixed certificate verifies the same fixed child root. -/
theorem recoverComponent_certificate (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (plan : RetryPlan R)
    (sk : SecretKey PP H plan.Coins S)
    (hend : sk.endpoints = endpoints hash sk.seed sk.starts)
    (p : UpperPosition S) (sig : GXMSS.Signature R H S.h S.v)
    (hsig : certificate hash family plan sk p = some sig) :
    recoverComponent hash family sk.seed p.1
      (internalMessage p (componentRoot hash sk.seed sk.endpoints (childTree S p))) sig =
      some (componentRoot hash sk.seed sk.endpoints p.val.1) := by
  cases hout : (certificateResult hash family plan sk p).output with
  | none => simp [certificate, hout] at hsig
  | some wr =>
      have heq : componentSignature hash sk p.1 wr = sig := by
        simpa [certificate, hout] using hsig
      rw [← heq]
      apply recoverComponent_componentSignature hash family sk hend
      have hv := RetryPlan.value_eq_some_of_run_output_eq_some plan
        (family.atEpoch p.val (Fin S.branching)) sk.seed
        (internalMessage p (componentRoot hash sk.seed sk.endpoints (childTree S p)))
        p.val.2 (sk.upperCoins p) hout
      simpa using hv

/-- Sequencing optional finite coordinates succeeds exactly when every coordinate succeeds. -/
theorem fin_mOfFn_eq_some_iff {α : Type} {n : ℕ} (f : Fin n → Option α) (xs : Fin n → α) :
    Fin.mOfFn n f = some xs ↔ ∀ i, f i = some (xs i) := by
  induction n with
  | zero =>
      have heq : xs = Fin.elim0 := by funext i; exact i.elim0
      simp [Fin.mOfFn, heq]
  | succ n ih =>
      constructor
      · intro h
        cases hhead : f 0 with
        | none => simp [Fin.mOfFn, hhead] at h
        | some head =>
            cases htail : Fin.mOfFn n (fun i => f i.succ) with
            | none => simp [Fin.mOfFn, hhead, htail] at h
            | some tail =>
                have heq : Fin.cons head tail = xs := by
                  simpa [Fin.mOfFn, hhead, htail] using h
                rw [← heq]
                intro i
                cases i using Fin.cases with
                | zero => exact hhead
                | succ i => exact (ih _ tail).mp htail i
      · intro h
        have hhead := h 0
        have htail := (ih (fun i => f i.succ) (fun i => xs i.succ)).mpr (fun i => h i.succ)
        simp only [Fin.mOfFn, hhead, htail, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        congr
        funext i
        cases i using Fin.cases <;> rfl

/-- A returned deterministic signature has honest bottom data and every fixed certificate. -/
theorem signWithCoins_success (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) (sig : Signature R H S)
    (hsig : signWithCoins hash family sampling sk ep msg coins = some sig) :
    (∃ wr, (componentResult family sampling.bottom sk (bottomPosition S ep)
      (bottomMessage ep msg) coins).output = some wr ∧
      sig.bottom = componentSignature hash sk (bottomPosition S ep) wr) ∧
    ∀ i, certificate hash family sampling.internal sk (upperPositionAt S ep i) =
      some (sig.upper i) := by
  cases hbottom : (componentResult family sampling.bottom sk (bottomPosition S ep)
      (bottomMessage ep msg) coins).output with
  | none => simp [signWithCoins, hbottom] at hsig
  | some wr =>
      cases hupper : Fin.mOfFn (S.d - 1) (fun i =>
          certificate hash family sampling.internal sk (upperPositionAt S ep i)) with
      | none => simp [signWithCoins, hbottom, hupper] at hsig
      | some upper =>
          have heq : (⟨componentSignature hash sk (bottomPosition S ep) wr, upper⟩ :
              Signature R H S) = sig := by
            simpa [signWithCoins, hbottom, hupper] using hsig
          subst sig
          exact ⟨⟨wr, rfl, rfl⟩, (fin_mOfFn_eq_some_iff _ upper).mp hupper⟩

/-- Every honestly returned layer recovers its actual component root. -/
theorem recoverThrough_signWithCoins (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S)
    (hend : sk.endpoints = endpoints hash sk.seed sk.starts)
    (ep : Epoch S) (msg : M) (coins : sampling.bottom.Coins) (sig : Signature R H S)
    (hsig : signWithCoins hash family sampling sk ep msg coins = some sig)
    (layer : ℕ) (hlayer : layer < S.d) :
    recoverThrough hash family sk.seed ep msg sig layer hlayer =
      some (componentRoot hash sk.seed sk.endpoints (positionAt S ep ⟨layer, hlayer⟩).1) := by
  obtain ⟨hbottom, hupper⟩ :=
    signWithCoins_success hash family sampling sk ep msg coins sig hsig
  induction layer with
  | zero =>
      obtain ⟨wr, hwr, hbottom⟩ := hbottom
      simp only [recoverThrough, hbottom]
      apply recoverComponent_componentSignature hash family sk hend
      have hv := RetryPlan.value_eq_some_of_run_output_eq_some sampling.bottom
        (family.atEpoch (bottomPosition S ep) (Fin S.branching)) sk.seed
        (bottomMessage ep msg) (bottomPosition S ep).2 coins hwr
      simpa using hv
  | succ layer ih =>
      let i : Fin (S.d - 1) := ⟨layer, by omega⟩
      have hchild : childTree S (upperPositionAt S ep i) =
          (positionAt S ep ⟨layer, by omega⟩).1 := by
        simpa [upperPositionAt, upperLayer, i] using
          childTree_positionAt S ep (upperLayer S i) (by simp [upperLayer])
      simp only [recoverThrough, ih (by omega), Option.bind_eq_bind, Option.bind_some]
      rw [← hchild]
      exact recoverComponent_certificate hash family sampling.internal sk hend
        (upperPositionAt S ep i) (sig.upper i) (hupper i)

/-- Every deterministic successful signature verifies for a consistent raw key pair. -/
theorem verify_signWithCoins [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S)
    (hc : Consistent hash pk sk) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) (sig : Signature R H S)
    (hsig : signWithCoins hash family sampling sk ep msg coins = some sig) :
    verify hash family pk ep msg sig = true := by
  rcases hc with ⟨hseed, hend, hroot⟩
  simp only [verify, hseed, recoverRoot]
  rw [recoverThrough_signWithCoins hash family sampling sk hend ep msg coins sig hsig,
    positionAt_topTree, ← hroot]
  simp

/-- Runtime-producible successful signatures verify, without conditioning away signing failure. -/
theorem verify_of_mem_support_sign [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H sampling.internal.Coins S)
    (hc : Consistent hash pk sk) (ep : Epoch S) (msg : M) (sig : Signature R H S)
    (hsig : some sig ∈ support (sign hash family sampling sk ep msg)) :
    verify hash family pk ep msg sig = true := by
  simp only [sign, support_map, Set.mem_image] at hsig
  obtain ⟨coins, _, hcoins⟩ := hsig
  exact verify_signWithCoins hash family sampling pk sk hc ep msg coins sig hcoins

/-- Optional finite sequencing fails exactly when one of its coordinates fails. -/
theorem fin_mOfFn_eq_none_iff {α : Type} {n : ℕ} (f : Fin n → Option α) :
    Fin.mOfFn n f = none ↔ ∃ i, f i = none := by
  classical
  constructor
  · intro h
    by_contra hn
    have hall : ∀ i, ∃ a, f i = some a := by
      intro i
      cases hi : f i with
      | none => exact False.elim (hn ⟨i, hi⟩)
      | some a => exact ⟨a, rfl⟩
    choose xs hxs using hall
    have hs := (fin_mOfFn_eq_some_iff f xs).mpr hxs
    rw [h] at hs
    contradiction
  · rintro ⟨i, hi⟩
    cases hs : Fin.mOfFn n f with
    | none => rfl
    | some xs =>
        have hc := (fin_mOfFn_eq_some_iff f xs).mp hs i
        rw [hi] at hc
        contradiction

/-- Full signing failure retains either bottom exhaustion or a failed fixed certificate. -/
theorem signWithCoins_eq_none_iff (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (sk : SecretKey PP H sampling.internal.Coins S) (ep : Epoch S) (msg : M)
    (coins : sampling.bottom.Coins) :
    signWithCoins hash family sampling sk ep msg coins = none ↔
      (componentResult family sampling.bottom sk (bottomPosition S ep)
        (bottomMessage ep msg) coins).output = none ∨
      ∃ i, certificate hash family sampling.internal sk (upperPositionAt S ep i) = none := by
  cases hb : (componentResult family sampling.bottom sk (bottomPosition S ep)
      (bottomMessage ep msg) coins).output with
  | none => simp [signWithCoins, hb]
  | some wr =>
      rw [← fin_mOfFn_eq_none_iff]
      cases hu : Fin.mOfFn (S.d - 1) (fun i =>
          certificate hash family sampling.internal sk (upperPositionAt S ep i)) <;>
        simp [signWithCoins, hb, hu]

/-- Strategy-dependent bounds on actual single-coordinate retry exhaustion.
The internal bound ranges over arbitrary child-root messages, before averaging key generation. -/
@[expose] def RetryFailureBounds (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (bottomError internalError : ℝ≥0∞) : Prop :=
  (∀ pp ep msg, Pr{let coins ← sampling.sampleBottom}[
    (sampling.bottom.run (family.atEpoch (bottomPosition S ep) (Fin S.branching)) pp
      (bottomMessage ep msg) (bottomPosition S ep).2 coins).output = none] ≤ bottomError) ∧
  (∀ pp (p : UpperPosition S) (root : H), Pr{let coins ← sampling.sampleInternal}[
    (sampling.internal.run (family.atEpoch p.val (Fin S.branching)) pp
      (internalMessage p root) p.val.2 coins).output = none] ≤ internalError)

private theorem fixed_keys_sign_failure_le (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (sampling : RetrySampling R)
    (bottomError internalError : ℝ≥0∞)
    (herrors : RetryFailureBounds family sampling bottomError internalError)
    (pp : PP) (starts : OTSPosition S → Fin S.v → H) (ep : Epoch S) (msg : M) :
    Pr{let coins ← sampleUpperCoins S sampling.sampleInternal
       let bottom ← sampling.sampleBottom}[
      signWithCoins hash family sampling (keys hash pp starts coins).2 ep msg bottom = none] ≤
        bottomError + (S.d - 1 : ℕ) * internalError := by
  classical
  let joint := do
    let coins ← sampleUpperCoins S sampling.sampleInternal
    let bottom ← sampling.sampleBottom
    pure (coins, bottom)
  let bottomBad := fun
      coins : (UpperPosition S → sampling.internal.Coins) × sampling.bottom.Coins =>
    (sampling.bottom.run (family.atEpoch (bottomPosition S ep) (Fin S.branching)) pp
      (bottomMessage ep msg) (bottomPosition S ep).2 coins.2).output = none
  let upperBad := fun i
      (coins : (UpperPosition S → sampling.internal.Coins) × sampling.bottom.Coins) =>
    certificate hash family sampling.internal (keys hash pp starts coins.1).2
      (upperPositionAt S ep i) = none
  have hbottom : Pr{let coins ← joint}[bottomBad coins] ≤ bottomError := by
    simpa [joint, bottomBad, prEvent_norm] using herrors.1 pp ep msg
  have hupper : ∀ i, Pr{let coins ← joint}[upperBad i coins] ≤ internalError := by
    intro i
    let p := upperPositionAt S ep i
    let root := componentRoot hash pp (endpoints hash pp starts) (childTree S p)
    let event := fun coins : sampling.internal.Coins =>
      (sampling.internal.run (family.atEpoch p.val (Fin S.branching)) pp
        (internalMessage p root) p.val.2 coins).output = none
    let : Fintype (UpperPosition S) := Fintype.ofFinite _
    have hmarginal := prEvent_coord_mPi_le
      (fun _ : UpperPosition S => sampling.sampleInternal) p event
    have hbound := hmarginal.trans (herrors.2 pp p root)
    have hdrop : Pr{let all ← sampleUpperCoins S sampling.sampleInternal
                    let _ ← sampling.sampleBottom}[event (all p)] =
        Pr{let all ← sampleUpperCoins S sampling.sampleInternal}[event (all p)] := by
      have hd := EvalDistEq.bind_congr
        (EvalDistEq.refl (sampleUpperCoins S sampling.sampleInternal))
        (fun all => EvalDistEq.bind_const sampling.sampleBottom (pure (all p)))
      simpa only [prEvent_norm] using hd.prEvent_eq event
    change Pr{let all ← sampleUpperCoins S sampling.sampleInternal}[event (all p)] ≤
      internalError at hbound
    rw [← hdrop] at hbound
    simpa [joint, upperBad, certificate, certificateResult, componentResult, keys,
      sampleUpperCoins, p, root, event, prEvent_norm] using hbound
  have hunion := prEvent_or_le joint bottomBad (fun coins => ∃ i, upperBad i coins)
  have htotal := hunion.trans
    (add_le_add hbottom (prEvent_exists_le_card_mul joint upperBad hupper))
  simpa [joint, bottomBad, upperBad, prEvent_norm, signWithCoins_eq_none_iff,
    componentResult, keys] using htotal

/-- Actual keygen/sign exhaustion, including fixed internal certificate failure. -/
noncomputable def failureExperiment [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (ep : Epoch S) (msg : M) : ProbComp Bool := do
  let keys ← keygen hash sampling
  let out ← sign hash family sampling keys.2 ep msg
  pure out.isNone

/-- Key-generation-averaged full-signature failure has the finite path union bound.
This uses the actual per-kind strategy failure probabilities, including correlated retry plans. -/
theorem failureExperiment_probability_le [SampleableType H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (bottomError internalError : ℝ≥0∞)
    (herrors : RetryFailureBounds family sampling bottomError internalError)
    (ep : Epoch S) (msg : M) :
    Pr{let failed ← failureExperiment hash family sampling ep msg}[failed = true] ≤
      bottomError + (S.d - 1 : ℕ) * internalError := by
  unfold failureExperiment keygen sign
  simp only [bind_assoc, pure_bind, bind_map_left]
  apply prEvent_bind_le_of_forall_le
  intro pp
  apply prEvent_bind_le_of_forall_le
  intro starts
  simpa [prEvent_norm] using fixed_keys_sign_failure_le hash family sampling
    bottomError internalError herrors pp starts ep msg

/-- Verification averaged over actual key generation equals one minus full signing exhaustion. -/
theorem averageSuccessMass_eq_one_sub_failure [SampleableType H] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (ep : Epoch S) (msg : M) :
    (scheme hash family sampling).averageSuccessMass ProbCompRuntime.probComp ep msg =
      1 - Pr{let failed ← failureExperiment hash family sampling ep msg}[failed = true] := by
  rw [← OracleComp.prEvent_not_eq_one_sub]
  rw [SyncSignatureAlg.averageSuccessMass, ProbCompRuntime.probComp_evalDist,
    ← prEvent_eq_evalDist_singleton]
  simp only [SyncSignatureAlg.averageCorrectnessExperiment, failureExperiment, scheme,
    keygen, sign, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply congrArg prEvent
  apply bind_congr
  intro pp
  apply bind_congr
  intro starts
  apply bind_congr
  intro upper
  apply bind_congr
  intro coins
  cases hs : signWithCoins hash family sampling (keys hash pp starts upper).2 ep msg coins with
  | none => simp [SyncSignatureAlg.accepts]
  | some sig =>
      have hv := verify_signWithCoins hash family sampling _ _
        (consistent_keys hash pp starts upper) ep msg coins sig hs
      simp [SyncSignatureAlg.accepts, hv]

/-- Averaged correctness for the actual forest key generator and its fixed optional certificates.
The conclusion is separate from the unchanged per-generated-key Complete predicate. -/
theorem average_complete [SampleableType H] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (bottomError internalError : ℝ≥0∞)
    (herrors : RetryFailureBounds family sampling bottomError internalError) :
    (scheme hash family sampling).AverageComplete ProbCompRuntime.probComp
      (bottomError + (S.d - 1 : ℕ) * internalError) := by
  intro ep msg
  rw [averageSuccessMass_eq_one_sub_failure]
  exact tsub_le_tsub_left (failureExperiment_probability_le hash family sampling
    bottomError internalError herrors ep msg) 1

private theorem iid_retry_failure_probability [SampleableType R]
    {E : Type} {n radix : ℕ} (enc : IncomparableEncoding PP M R E n radix)
    (pp : PP) (msg : M) (ep : E) (budget : ℕ) :
    Pr{let coins ← ($ᵗ (RetryPlan.iid R budget).Coins)}[
      ((RetryPlan.iid R budget).run enc pp msg ep coins).output = none] =
      (Pr{let r ← ($ᵗ R)}[enc.value pp msg r ep = none]) ^ budget := by
  let : MeasurableSpace R := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
  exact RetryPlan.iid_exhaustion_mass enc pp msg ep budget

/-- Independent retry coins give the per-kind power bounds from one-attempt error bounds. -/
theorem retryFailureBounds_iid [SampleableType R] (family : EncodingFamily PP M R H S)
    (bottomBudget internalBudget : ℕ) (bottomError internalError : ℝ≥0∞)
    (hbottom : ∀ pp ep msg,
      Pr{let r ← ($ᵗ R)}[family.value (bottomPosition S ep) pp
        (bottomMessage ep msg) r = none] ≤ bottomError)
    (hinternal : ∀ pp (p : UpperPosition S) (root : H),
      Pr{let r ← ($ᵗ R)}[family.value p.val pp
        (internalMessage p root) r = none] ≤ internalError) :
    RetryFailureBounds family (RetrySampling.iid bottomBudget internalBudget)
      (bottomError ^ bottomBudget) (internalError ^ internalBudget) := by
  constructor
  · intro pp ep msg
    change Pr{let coins ← ($ᵗ (RetryPlan.iid R bottomBudget).Coins)}[
      ((RetryPlan.iid R bottomBudget).run
        (family.atEpoch (bottomPosition S ep) (Fin S.branching)) pp
        (bottomMessage ep msg) (bottomPosition S ep).2 coins).output = none] ≤ _
    rw [iid_retry_failure_probability]
    exact pow_le_pow_left' (by simpa using hbottom pp ep msg) bottomBudget
  · intro pp p root
    change Pr{let coins ← ($ᵗ (RetryPlan.iid R internalBudget).Coins)}[
      ((RetryPlan.iid R internalBudget).run (family.atEpoch p.val (Fin S.branching)) pp
        (internalMessage p root) p.val.2 coins).output = none] ≤ _
    rw [iid_retry_failure_probability]
    exact pow_le_pow_left' (by simpa using hinternal pp p root) internalBudget

/-- Keygen-averaged correctness under IID retries has error at most
`δ_bottom^K_bottom + (d-1)*δ_internal^K_internal`.
Counter plans retain their own strategy-dependent failure law. -/
theorem average_complete_iid [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (bottomBudget internalBudget : ℕ) (bottomError internalError : ℝ≥0∞)
    (hbottom : ∀ pp ep msg,
      Pr{let r ← ($ᵗ R)}[family.value (bottomPosition S ep) pp
        (bottomMessage ep msg) r = none] ≤ bottomError)
    (hinternal : ∀ pp (p : UpperPosition S) (root : H),
      Pr{let r ← ($ᵗ R)}[family.value p.val pp
        (internalMessage p root) r = none] ≤ internalError) :
    (scheme hash family (RetrySampling.iid bottomBudget internalBudget)).AverageComplete
      ProbCompRuntime.probComp
      (bottomError ^ bottomBudget + (S.d - 1 : ℕ) * internalError ^ internalBudget) :=
  average_complete hash family _ _ _
    (retryFailureBounds_iid family bottomBudget internalBudget bottomError internalError
      hbottom hinternal)

end GXMSS.Hypertree
