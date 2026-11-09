/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling
import all HashSig.GXMSS.Hypertree.PRFDerivedScheme
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
public import HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
public import VCVio.EvalDist.IndepProductMeasure

/-!
# One shared function-oracle hypertree interaction

Setup requests use the actual layout domain and retain one signing core. IID setup requests one
response per start; paired setup requests one complete response per start group. All internal
retry tapes are fixed once before adaptive signing. Duplicate global requests are rejected
before any fresh retry request. The ideal PRF interpreter retains one complete-response cache
through setup and all signing calls.
-/

public section

namespace GXMSS.Hypertree.PRFDerived.Unforgeability

open OracleComp OracleSpec Encoding
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.SigningSimulation

variable {PP T X H M R Response Key : Type} {S : Shape}

/-- One named PRF distinguisher observes the complete interaction's actual strong winning bit. -/
noncomputable def randgenPRFReduction [DecidableEq H] [DecidableEq M]
    [DecidableEq (Hypertree.Signature R H S)] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) (adv : SchemeAdversary PP H M R S) :
    OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response) Bool :=
  SyncSignatureUnforgeability.strongValid
    (oracleScheme hash family layout sampling interpretation retry) <$>
      oracleInteraction hash family layout sampling interpretation retry adv

/-- Retry response queries have the exact pure-evaluator interpretation. -/
theorem responseFamilyQueries_real {D : Type} (layout : Layout) (budget : ℕ)
    (input : RetryIndex layout budget → D) (prf : PRFScheme Key D Response)
    (key : Key) :
    simulateQ (prf.prfRealQueryImpl key) (responseFamilyQueries layout budget input) =
      pure (fun i => prf.eval key (input i)) := by
  cases layout with
  | iid =>
      exact simulateQ_fin_mOfFn_pure _ _ _ (fun _ => by simp)
  | pairedCounter => simp [responseFamilyQueries]


private theorem simulate_mPi_pure {ι I A : Type} {spec : OracleSpec ι} [Fintype I]
    (impl : QueryImpl spec ProbComp) (f : I → OracleComp spec A) (g : I → A)
    (h : ∀ i, simulateQ impl (f i) = pure (g i)) :
    simulateQ impl (Fintype.mPi f) = pure g := by
  unfold Fintype.mPi
  rw [simulateQ_map, simulateQ_fin_mOfFn_pure
    (g := fun k => g ((Fintype.equivFin I).symm k)) (hfg := fun k => h _)]
  simp only [map_pure]
  congr 1
  funext i
  simp [Equiv.arrowCongr]

/-- Grouped setup reads one complete response per group in the real world. -/
theorem startQueries_real (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response) (pp : PP)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key) :
    simulateQ (prf.prfRealQueryImpl key) (startQueries layout sampling interpretation pp) =
      pure (PRFDerived.starts layout (retryBudget sampling) prf.eval interpretation key pp) := by
  let : Fintype (OTSPosition S) := Fintype.ofFinite _
  unfold startQueries
  apply simulate_mPi_pure
  intro p
  cases layout with
  | iid =>
      apply simulateQ_fin_mOfFn_pure
      intro i
      simp [PRFDerived.starts]
  | pairedCounter =>
      rw [simulateQ_bind, simulateQ_fin_mOfFn_pure
        (g := fun group => interpretation.chainPair (prf.eval key (.start pp p group)))
        (hfg := fun _ => by simp)]
      simp [PRFDerived.starts]

/-- Bottom coins under the real function oracle are the construction's exact finite coins. -/
theorem bottomCoinsQuery_real (layout : Layout) (sampling : RetrySampling R)
    (retry : RetryInterpretation layout sampling Response) (pp : PP) (ep : Epoch S) (msg : M)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key) :
    simulateQ (prf.prfRealQueryImpl key) (bottomCoinsQuery layout sampling retry pp ep msg) =
      pure (retry.bottomCoins fun i => prf.eval key
        (.retry pp (bottomPosition S ep) (bottomMessage ep msg)
          (bottomRetryIndex layout sampling ep i))) := by
  rw [bottomCoinsQuery, simulateQ_map, responseFamilyQueries_real]
  rfl

/-- Internal coins under the real function oracle use the fixed child-root message. -/
theorem internalCoinsQuery_real (layout : Layout) (sampling : RetrySampling R)
    (retry : RetryInterpretation layout sampling Response) (pp : PP)
    (p : UpperPosition S) (root : H)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key) :
    simulateQ (prf.prfRealQueryImpl key) (internalCoinsQuery layout sampling retry pp p root) =
      pure (retry.internalCoins fun i => prf.eval key (.retry pp p.val (internalMessage p root)
        (internalRetryIndex layout sampling p i))) := by
  rw [internalCoinsQuery, simulateQ_map, responseFamilyQueries_real]
  rfl

/-- Real setup retains exactly the direct deterministic construction's complete signing core. -/
theorem keyMaterialQueries_real (hash : HashInstance PP T X H S) (layout : Layout)
    (sampling : RetrySampling R) (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key) :
    simulateQ (prf.prfRealQueryImpl key)
      (keyMaterialQueries hash layout sampling interpretation retry) =
      pure ((PRFDerived.keys hash layout sampling prf.eval interpretation retry key).1,
        coreSecretKey hash layout sampling prf.eval interpretation retry key) := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  unfold keyMaterialQueries
  simp only [simulateQ_bind, simulateQ_map,
    PRFScheme.simulateQ_prfRealQueryImpl_functionQuery, map_pure, pure_bind]
  rw [startQueries_real]
  simp only [pure_bind]
  change (simulateQ (prf.prfRealQueryImpl key) (Fintype.mPi _) >>= _) = _
  rw [simulate_mPi_pure _ _ _
    (fun p => internalCoinsQuery_real _ _ _ _ p _ prf key)]
  simp [PRFDerived.keys, coreSecretKey, Hypertree.keys, publicSeed]

private def fixedKeyScheme [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key) :
    SyncSignatureAlg ProbComp M (GXMSS.PublicKey PP H) Key
      (Hypertree.Signature R H S) (Epoch S) where
  keygen := pure (PRFDerived.keys hash layout sampling prf.eval interpretation retry key)
  sign := PRFDerived.sign hash family layout sampling prf.eval interpretation retry
  verify := Hypertree.verify hash family

private theorem oracleSign_real [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key)
    (ep : Epoch S) (msg : M) :
    simulateQ (prf.prfRealQueryImpl key)
      ((oracleScheme hash family layout sampling interpretation retry).sign
        (coreSecretKey hash layout sampling prf.eval interpretation retry key) ep msg) =
      PRFDerived.sign hash family layout sampling prf.eval interpretation retry key ep msg := by
  simp only [oracleScheme, simulateQ_bind]
  rw [bottomCoinsQuery_real]
  rfl

private def fixedKeyHandler [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Hypertree.Signature R H S))
      (StateT (SyncSignatureUnforgeability.History (Epoch S) M (Hypertree.Signature R H S))
        ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History (Epoch S) M (Hypertree.Signature R H S))
      ProbComp) +
    SyncSignatureUnforgeability.signingOracle
      (fixedKeyScheme hash family layout sampling interpretation retry prf key) key

private theorem signingHandler_real [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch S) M
      (Hypertree.Signature R H S)).Domain)
    (history : SyncSignatureUnforgeability.History (Epoch S) M (Hypertree.Signature R H S)) :
    simulateQ (prf.prfRealQueryImpl key)
      ((signingHandler (oracleScheme hash family layout sampling interpretation retry)
        (coreSecretKey hash layout sampling prf.eval interpretation retry key) q).run history) =
      (fixedKeyHandler hash family layout sampling interpretation retry prf key q).run history := by
  cases q with
  | inl q =>
      simp [signingHandler, fixedKeyHandler, QueryImpl.liftTarget,
        PRFScheme.prfRealQueryImpl, QueryImpl.passthrough_add]
  | inr request =>
      rcases request with ⟨ep, msg⟩
      simp only [signingHandler, fixedKeyHandler, QueryImpl.add_apply_inr]
      change simulateQ _ (SyncSignatureUnforgeability.signingOracle _ _ (ep, msg) history) =
        SyncSignatureUnforgeability.signingOracle _ _ (ep, msg) history
      cases hu : history ep with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          rw [SyncSignatureUnforgeability.signingOracle_used (h := hu),
            SyncSignatureUnforgeability.signingOracle_used (h := hu)]
          simp
      | none =>
          rw [SyncSignatureUnforgeability.signingOracle_unused (h := hu),
            SyncSignatureUnforgeability.signingOracle_unused (h := hu)]
          rw [simulateQ_bind, oracleSign_real]
          simp [fixedKeyScheme]

/-- The real shared-oracle interaction preserves the full fixed-key source observation. -/
private theorem oracleInteraction_real [DecidableEq H] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (key : Key)
    (adv : SchemeAdversary PP H M R S) :
    simulateQ (prf.prfRealQueryImpl key)
      (oracleInteraction hash family layout sampling interpretation retry adv) =
      SyncSignatureUnforgeability.interaction
        (fixedKeyScheme hash family layout sampling interpretation retry prf key) adv := by
  unfold oracleInteraction
  rw [simulateQ_bind, keyMaterialQueries_real]
  simp only [pure_bind, simulateQ_bind]
  rw [simulateQ_StateT_compose _ _
    (fixedKeyHandler hash family layout sampling interpretation retry prf key)
    (signingHandler_real hash family layout sampling interpretation retry prf key)]
  rfl

/-- The named real PRF experiment is the actual PRF-derived strong game. -/
theorem randgenPRFReduction_real_strong [DecidableEq H] [DecidableEq M]
    [DecidableEq (Hypertree.Signature R H S)] (hash : HashInstance PP T X H S)
    (family : EncodingFamily PP M R H S) (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response)
    (prf : PRFScheme Key (Domain PP M H R S layout sampling) Response)
    (adv : SchemeAdversary PP H M R S) :
    prf.prfRealExperiment
      (randgenPRFReduction hash family layout sampling interpretation retry adv) =
      SyncSignatureUnforgeability.strongValid
        (PRFDerived.scheme hash family layout sampling prf interpretation retry) <$>
        SyncSignatureUnforgeability.interaction
          (PRFDerived.scheme hash family layout sampling prf interpretation retry) adv := by
  unfold PRFScheme.prfRealExperiment randgenPRFReduction
  simp only [simulateQ_map, oracleInteraction_real]
  simp only [SyncSignatureUnforgeability.interaction, PRFDerived.scheme, PRFDerived.keygen,
    map_eq_bind_pure_comp, bind_assoc, fixedKeyScheme, pure_bind]
  rfl

end GXMSS.Hypertree.PRFDerived.Unforgeability
