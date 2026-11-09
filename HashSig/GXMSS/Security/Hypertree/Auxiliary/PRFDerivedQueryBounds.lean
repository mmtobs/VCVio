/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Reductions.PRFDerivedOracleInteraction
import all HashSig.GXMSS.Security.Hypertree.Reductions.PRFDerivedOracleInteraction
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.PRFDerivedSampling
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedResponseCache
import all HashSig.GXMSS.Security.Auxiliary.PRFDerivedSigningSimulation
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-! # Query counts for the actual eager shared-oracle reduction -/

public section

namespace GXMSS.Hypertree.PRFDerived.Unforgeability
open OracleComp OracleSpec
open GXMSS.PRFDerived.ResponseCache GXMSS.PRFDerived.SigningSimulation

variable {PP T X H M R Response : Type} {S : Shape}

/-- One start group supplies two halves in the grouped layout. -/
@[expose] def startQueryCount (S : Shape) : Layout → ℕ
  | .iid => S.v
  | .pairedCounter => (S.v + 1) / 2

/-- A counter family always queries one base, including a zero-attempt family. -/
@[expose] def retryQueryCount : Layout → ℕ → ℕ
  | .iid, budget => budget
  | .pairedCounter, _ => 1

/-- Actual eager function-call cap; public hash trials are not function-oracle requests. -/
@[expose] def eagerQueryBound (S : Shape) (layout : Layout)
    (sampling : RetrySampling R) (qs : ℕ) : ℕ :=
  1 + otsCount S * startQueryCount S layout +
    upperCount S * retryQueryCount layout sampling.internal.budget +
    qs * retryQueryCount layout sampling.bottom.budget

/-- The IID eager bound has one response per start and retry attempt. -/
theorem eagerQueryBound_iid (S : Shape) (sampling : RetrySampling R) (qs : ℕ) :
    eagerQueryBound S .iid sampling qs =
      1 + otsCount S * S.v + upperCount S * sampling.internal.budget +
        qs * sampling.bottom.budget := rfl

/-- Grouped layout counts actual pairs and base requests. -/
theorem eagerQueryBound_pairedCounter (S : Shape) (sampling : RetrySampling R) (qs : ℕ) :
    eagerQueryBound S .pairedCounter sampling qs =
      1 + otsCount S * ((S.v + 1) / 2) + upperCount S + qs := by
  simp [eagerQueryBound, startQueryCount, retryQueryCount]

private theorem total_map {ι A B : Type} {spec : OracleSpec ι}
    {oa : OracleComp spec A} (f : A → B) {n : ℕ} (h : IsTotalQueryBound oa n) :
    IsTotalQueryBound (f <$> oa) n := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def, Nat.add_zero] using
    isTotalQueryBound_bind h (fun _ => (show IsTotalQueryBound (pure (f _) :
      OracleComp spec B) 0 from trivial))

private theorem total_mPi {ι I A : Type} {spec : OracleSpec ι} [Fintype I]
    (f : I → OracleComp spec A) (n : ℕ) (h : ∀ i, IsTotalQueryBound (f i) n) :
    IsTotalQueryBound (Fintype.mPi f) (Fintype.card I * n) := by
  unfold Fintype.mPi
  apply total_map
  exact query_bound_fin_mOfFn _ (fun i => h _)

/-- Response-family queries count distinct IID indices or one grouped base. -/
theorem responseFamilyQueries_bound {D : Type} (layout : Layout) (budget : ℕ)
    (input : RetryIndex layout budget → D) :
    IsTotalQueryBound (responseFamilyQueries (Response := Response) layout budget input)
      (retryQueryCount layout budget) := by
  cases layout with
  | iid =>
      simpa [responseFamilyQueries, retryQueryCount] using
        query_bound_fin_mOfFn (fun i => PRFScheme.functionQuery (R := Response) (input i))
          (fun _ => functionQuery_bound _)
  | pairedCounter => exact total_map _ (functionQuery_bound _)

/-- Setup start calls count the actual layout-indexed groups. -/
theorem startQueries_bound (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response) (pp : PP) :
    IsTotalQueryBound (startQueries (M := M) (S := S) layout sampling interpretation pp)
      (otsCount S * startQueryCount S layout) := by
  let : Fintype (OTSPosition S) := Fintype.ofFinite _
  have hc : Fintype.card (OTSPosition S) = otsCount S := by
    rw [← Nat.card_eq_fintype_card, card_otsPosition]
  rw [← hc]
  unfold startQueries
  dsimp only
  apply total_mPi
  intro p
  cases layout with
  | iid =>
      simpa only [startQueryCount, Nat.mul_one] using
        query_bound_fin_mOfFn (fun i : Fin S.v => interpretation.chainStart <$>
          PRFScheme.functionQuery (R := Response)
            (.start pp p i : Domain PP M H R S .iid sampling))
          (fun _ => total_map _ (functionQuery_bound _))
  | pairedCounter =>
      have h := query_bound_fin_mOfFn (fun i : Fin ((S.v + 1) / 2) =>
        interpretation.chainPair <$> PRFScheme.functionQuery (R := Response)
          (.start pp p i : Domain PP M H R S .pairedCounter sampling))
        (fun _ => total_map _ (functionQuery_bound _))
      simpa only [startQueryCount, Nat.mul_one, Nat.add_zero] using
        isTotalQueryBound_bind h (fun pairs => (show IsTotalQueryBound
          (pure (fun i : Fin S.v => if (startHalf i).val = 0 then
            (pairs (startGroup S i)).1 else (pairs (startGroup S i)).2) :
              OracleComp (PRFScheme.PRFOracleSpec
                (Domain PP M H R S .pairedCounter sampling) Response) _) 0 from trivial))

/-- Eager setup queries one seed, all start groups and all fixed internal retry families. -/
theorem keyMaterialQueries_bound (hash : HashInstance PP T X H S) (layout : Layout)
    (sampling : RetrySampling R) (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) :
    IsTotalQueryBound (keyMaterialQueries (M := M) hash layout sampling interpretation retry)
      (1 + otsCount S * startQueryCount S layout +
        upperCount S * retryQueryCount layout sampling.internal.budget) := by
  let : Fintype (UpperPosition S) := Fintype.ofFinite _
  have hc : Fintype.card (UpperPosition S) = upperCount S := by
    rw [← Nat.card_eq_fintype_card, card_upperPosition]
  unfold keyMaterialQueries
  dsimp only
  rw [Nat.add_assoc]
  apply isTotalQueryBound_bind (total_map _ (functionQuery_bound _))
  intro pp
  apply isTotalQueryBound_bind (startQueries_bound _ _ _ _)
  intro starts
  have h := total_mPi
    (fun p : UpperPosition S => internalCoinsQuery (M := M) layout sampling retry pp p
      (componentRoot hash pp (endpoints hash pp starts) (childTree S p)))
    (retryQueryCount layout sampling.internal.budget)
    (fun _ => total_map _ (responseFamilyQueries_bound _ _ _))
  simpa only [hc, Nat.add_zero] using isTotalQueryBound_bind h (fun coins =>
    (show IsTotalQueryBound (pure (Hypertree.keys hash pp starts coins) :
      OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response) _) 0
      from trivial))

/-- The named reduction uses only the eager setup cap and bounded fresh signing families.
Ambient uniform requests are uncharged; repeated signing requests are rejected before retries. -/
theorem randgenPRFReduction_query_bound [DecidableEq H] [DecidableEq M]
    [DecidableEq (Hypertree.Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (layout : Layout) (sampling : RetrySampling R)
    (interpretation : Interpretation PP H R Response)
    (retry : RetryInterpretation layout sampling Response) (qs : ℕ)
    (adv : SchemeAdversary PP H M R S)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    (randgenPRFReduction hash family layout sampling interpretation retry adv).IsQueryBoundP
      (fun q => q.isRight = true) (eagerQueryBound S layout sampling qs) := by
  have hsign (sk : Hypertree.SecretKey PP H sampling.internal.Coins S)
      (ep : Epoch S) (msg : M) :
      IsTotalQueryBound ((oracleScheme hash family layout sampling interpretation retry).sign
        sk ep msg) (retryQueryCount layout sampling.bottom.budget) := by
    unfold oracleScheme
    simpa only [bind_pure_comp, bottomCoinsQuery] using
      total_map (signWithCoins hash family sampling sk ep msg)
        (total_map retry.bottomCoins (responseFamilyQueries_bound _ _ _))
  unfold randgenPRFReduction
  rw [isQueryBoundP_map_iff]
  unfold oracleInteraction eagerQueryBound
  apply isQueryBoundP_bind (keyMaterialQueries_bound hash layout sampling interpretation retry
    |>.isQueryBoundP)
  intro pair _
  have hb := isQueryBoundP_simulateQ_run_weighted
    (signingHandler (oracleScheme hash family layout sampling interpretation retry) pair.2)
    (retryQueryCount layout sampling.bottom.budget)
    (fun q hq state => by
      simpa only [hq, ↓reduceIte] using signingHandler_query_bound
        (oracleScheme hash family layout sampling interpretation retry) pair.2 _ (hsign pair.2)
          q state)
    (fun q hq state => by
      have hq' : q.isRight = false := Bool.eq_false_iff.mpr hq
      simpa only [hq', Bool.false_eq_true, ↓reduceIte] using signingHandler_query_bound
        (oracleScheme hash family layout sampling interpretation retry) pair.2 _ (hsign pair.2)
          q state)
    (adv.forge pair.1) qs (hqueries pair.1) SyncSignatureUnforgeability.emptyHistory
  simpa only [Nat.add_zero, SyncSignatureUnforgeability.ExperimentResult] using
    isQueryBoundP_bind hb (fun result _ =>
    (show IsQueryBoundP (pure (pair.1, result.1, result.2) :
      OracleComp (PRFScheme.PRFOracleSpec (Domain PP M H R S layout sampling) Response) _)
        (fun q => q.isRight = true) 0 from trivial))

end GXMSS.Hypertree.PRFDerived.Unforgeability
