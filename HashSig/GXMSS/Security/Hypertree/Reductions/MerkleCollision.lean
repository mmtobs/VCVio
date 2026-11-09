/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.ForestWitnesses
import all HashSig.GXMSS.Security.Hypertree.Auxiliary.Interaction
import all HashSig.GXMSS.Hypertree.Scheme
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Global Merkle collision reduction

One seed-free choose phase registers the full forest. After the seed is revealed, the reduction
samples the actual fixed tapes, runs the native synchronized source adversary, and selects the
registered honest input of the extracted collision. No component is guessed before the forgery.
-/

public section

namespace GXMSS.Hypertree.Unforgeability

open OracleComp OracleSpec TweakableHash GXMSS.Security

variable {PP T X H M R : Type} {S : Shape}

/-- The authoritative target-collision decision for an explicit accepted challenge history. -/
@[expose] def candidateCheck [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (pp : PP) (history : List (T × X))
    (candidate : ℕ × X) : Bool :=
  match history[candidate.1]? with
  | none => false
  | some (t, first) => decide (candidate.2 ≠ first ∧
      hash.thf.eval pp t candidate.2 = hash.thf.eval pp t first)

/-- Failed extraction returns a total candidate; successful extraction retains orientation. -/
@[expose] def witnessCandidate [DecidableEq T] [DecidableEq X]
    (history : List (T × X)) (fallback : X) (witness : Option (HashCollision T X)) : ℕ × X :=
  match witness with
  | none => (0, fallback)
  | some collision => selectCollision history collision

/-- A sound registered witness passes exactly the native target-collision decision. -/
theorem candidateCheck_of_witness [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (pp : PP) (history : List (T × X))
    (collision : HashCollision T X) (hmem : (collision.tweak, collision.first) ∈ history)
    (hsound : collision.Sound hash.thf pp) :
    candidateCheck hash pp history (selectCollision history collision) = true := by
  rw [candidateCheck, selectCollision_lookup history collision hmem]
  exact decide_eq_true ⟨hsound.1.symm, hsound.2.symm⟩

/-- Canonical total Merkle fallback: the endpoint vector at leaf zero of the top component. -/
@[expose] def merkleFallbackInput (hash : HashInstance PP T X H S)
    (ends : OTSPosition S → Fin S.v → H) : X := hash.vectorInput (ends (topTree S, 0))

/-- Global full-forest reduction with an oracle-free post-forgery witness extractor. -/
@[expose] noncomputable def forestCollisionReduction [SampleableType H]
    [DecidableEq T] [DecidableEq X]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X)) :
    SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone hash.thf (merkleCapacity S)) where
  State := ForestSetupState T X H S
  choose := chooseForest hash (merkleCapacity S)
  forge state pp := do
    let coins ← sampleUpperCoins S sampling.sampleInternal
    let sk : SecretKey PP H sampling.internal.Coins S :=
      ⟨pp, state.starts, state.endpoints, coins⟩
    let pk : GXMSS.PublicKey PP H := ⟨state.roots (topTree S), pp⟩
    let out ← Security.runWithKeys hash family sampling adv pk sk
    pure (witnessCandidate state.targets (merkleFallbackInput hash state.endpoints) (find out))

/-- The named global Merkle target-collision reduction. -/
@[expose] noncomputable def merkleTargetCollisionReduction [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    [DecidableEq (GXMSS.Signature R H S.h S.v)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S) :=
  forestCollisionReduction hash family sampling adv (sourceMerkleWitness? hash family)

/-- The faithful native collision computation over an explicit global target ledger. -/
@[expose] noncomputable def collisionProgram [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (ledger : PP → (OTSPosition S → Fin S.v → H) →
      (OTSPosition S → Fin S.v → H) → List (T × X))
    (fallbackInput : H → (OTSPosition S → Fin S.v → H) → X)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X)) :
    ProbComp Bool := do
  let pp ← hash.thf.seedGen
  let fallback ← ($ᵗ H : ProbComp H)
  let starts ← sampleStarts S
  let coins ← sampleUpperCoins S sampling.sampleInternal
  let (pk, sk) := keys hash pp starts coins
  let registered := ledger pp starts sk.endpoints
  let out ← Security.runWithKeys hash family sampling adv pk sk
  pure (candidateCheck hash pp registered
    (witnessCandidate registered (fallbackInput fallback sk.endpoints) (find out)))

/-- The faithful native execution after complete global target registration. -/
@[expose] noncomputable def forestCollisionProgram [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X)) :
    ProbComp Bool := collisionProgram hash family sampling adv (setupLedger hash)
      (fun _ ends => merkleFallbackInput hash ends) find

/-- The authoritative full-forest experiment equals the faithful native source execution. -/
theorem forestCollisionReduction_experiment [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X))
    (hv : 0 < S.v) :
    SM_DT_TCR_Experiment (forestCollisionReduction hash family sampling adv find) =
      forestCollisionProgram hash family sampling adv find := by
  unfold SM_DT_TCR_Experiment forestCollisionReduction forestCollisionProgram collisionProgram
  apply bind_congr
  intro pp
  rw [chooseForest_run hash (merkleCapacity S) pp (setupCount_le_capacity S hv)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  apply bind_congr
  intro coins
  apply bind_congr
  intro out
  simp only [keys, candidateCheck, SM_DT_TCR_Problem.standalone]
  split
  · simp_all only
  · simp_all only [ne_eq, PFunctor.FreeM.pure_inj]
    exact decide_eq_decide.mpr Iff.rfl

/-- A registered sound extractor bounds a native observation on the same actual source execution. -/
theorem sourceFlag_le_collisionProgram [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (ledger : PP → (OTSPosition S → Fin S.v → H) →
      (OTSPosition S → Fin S.v → H) → List (T × X))
    (fallbackInput : H → (OTSPosition S → Fin S.v → H) → X)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X))
    (flag : Security.Result PP H M R sampling.internal.Coins S → Bool)
    (hfind : ∀ out, flag out = true → (find out).isSome)
    (hspec : ∀ out collision, find out = some collision →
      collision.Sound hash.thf out.sk.seed ∧ (collision.tweak, collision.first) ∈
        ledger out.sk.seed out.sk.starts out.sk.endpoints) :
    𝒟[flag <$> Security.sourceProgram hash family sampling adv] {true} ≤
      𝒟[collisionProgram hash family sampling adv ledger fallbackInput find] {true} := by
  have hpad : 𝒟[flag <$> Security.sourceProgram hash family sampling adv] = 𝒟[(do
      let pp ← hash.thf.seedGen
      let _fallback ← ($ᵗ H : ProbComp H)
      let starts ← sampleStarts S
      let coins ← sampleUpperCoins S sampling.sampleInternal
      let (pk, sk) := keys hash pp starts coins
      let out ← Security.runWithKeys hash family sampling adv pk sk
      pure (flag out) : ProbComp Bool)] := by
    unfold Security.sourceProgram keygen
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
    apply OracleComp.evalDist_bind_congr_of_support
    intro pp _
    exact (OracleComp.evalDist_bind_const ($ᵗ H : ProbComp H) _).symm
  rw [hpad]
  unfold collisionProgram
  apply OracleComp.evalDist_bind_apply_mono_of_support hash.thf.seedGen _ _ (by measurability)
  intro pp _
  apply OracleComp.evalDist_bind_apply_mono_of_support ($ᵗ H : ProbComp H) _ _ (by measurability)
  intro fallback _
  apply OracleComp.evalDist_bind_apply_mono_of_support (sampleStarts S) _ _ (by measurability)
  intro starts _
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (sampleUpperCoins S sampling.sampleInternal) _ _ (by measurability)
  intro coins _
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (Security.runWithKeys hash family sampling adv
      (keys hash pp starts coins).1 (keys hash pp starts coins).2) _ _ (by measurability)
  intro out hout
  obtain ⟨_, hsk, _⟩ := Security.runWithKeys_support_keys hash family sampling adv _ _ out hout
  by_cases hflag : flag out = true
  · obtain ⟨collision, hc⟩ := Option.isSome_iff_exists.mp (hfind out hflag)
    obtain ⟨hsound, hmem⟩ := hspec out collision hc
    rw [hsk] at hsound hmem
    have hwin := candidateCheck_of_witness hash pp
      (ledger pp starts (keys hash pp starts coins).2.endpoints) collision hmem hsound
    simp only [keys] at hwin
    simp [hflag, hc, witnessCandidate, hwin]
  · simp [Bool.eq_false_iff.mpr hflag]

/-- A source observation with a registered sound extractor is bounded by the actual global
full-forest target-collision experiment. This is a native successful-output mass comparison. -/
theorem forestCollisionReduction_bound [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S)
    (find : Security.Result PP H M R sampling.internal.Coins S → Option (HashCollision T X))
    (flag : Security.Result PP H M R sampling.internal.Coins S → Bool)
    (hv : 0 < S.v)
    (hfind : ∀ out, flag out = true → (find out).isSome)
    (hspec : ∀ out collision, find out = some collision →
      collision.Sound hash.thf out.sk.seed ∧ (collision.tweak, collision.first) ∈
        setupLedger hash out.sk.seed out.sk.starts out.sk.endpoints) :
    𝒟[flag <$> Security.sourceProgram hash family sampling adv] {true} ≤
      SM_DT_TCR_Advantage (forestCollisionReduction hash family sampling adv find) := by
  rw [SM_DT_TCR_Advantage, forestCollisionReduction_experiment hash family sampling adv find hv]
  exact sourceFlag_le_collisionProgram hash family sampling adv (setupLedger hash)
    (fun _ ends => merkleFallbackInput hash ends) find flag hfind hspec

/-- The globally selected Merkle bad mass is charged to the single named actual hash game. -/
theorem sourceMerkleBad_le_targetCollision [SampleableType H]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H S.h S.v)] [DecidableEq (Signature R H S)]
    (hash : HashInstance PP T X H S) (family : EncodingFamily PP M R H S)
    (sampling : RetrySampling R) (adv : Security.SchemeAdversary PP H M R S) (hv : 0 < S.v) :
    𝒟[sourceMerkleBad hash family sampling <$> Security.sourceProgram hash family sampling adv]
      {true} ≤ SM_DT_TCR_Advantage (merkleTargetCollisionReduction hash family sampling adv) := by
  apply forestCollisionReduction_bound hash family sampling adv (sourceMerkleWitness? hash family)
    (sourceMerkleBad hash family sampling) hv
  · intro out h
    simp only [sourceMerkleBad, Bool.and_eq_true] at h
    exact h.2
  · exact sourceMerkleWitness?_spec hash family

end GXMSS.Hypertree.Unforgeability
