/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Hypertree.Completeness
public import HashSig.GXMSS.Hypertree.PRFDerivedScheme
import all HashSig.GXMSS.Merkle
import all HashSig.GXMSS.Chain
public meta import HashSigTest.GXMSS.TrustAuditSupport

/-! # Hypertree construction and failure controls

Small height-zero forests exercise all layers without enumerating a large key space. A fixed
failed intermediate certificate prevents every request through it from returning a signature.
-/

public section

namespace GXMSS.Hypertree.Test

open Encoding

/-- Tiny height-zero forests used by construction controls. -/
@[expose] def shape (extra : ℕ) : Shape := ⟨extra + 1, 0, 1, 1, by omega⟩
private abbrev Input := Bool ⊕ ((Bool × Bool) ⊕ (Fin 1 → Bool))
private abbrev Tweak (extra : ℕ) :=
  ChainPosition (shape extra) ⊕
    (TreePosition (shape extra) × Fin ((shape extra).h + 1) × Fin (shape extra).branching)

private def hash (extra : ℕ) : HashInstance Unit (Tweak extra) Input Bool (shape extra) where
  thf := ⟨pure (), fun _ _ input => match input with
    | .inl b => !b
    | .inr (.inl (a, b)) => xor a b
    | .inr (.inr values) => values 0⟩
  digestInput := Function.Embedding.inl
  pairInput := Function.Embedding.inl.trans Function.Embedding.inr
  vectorInput := Function.Embedding.inr.trans Function.Embedding.inr
  chainTweak := Function.Embedding.inl
  treeTweak := Function.Embedding.inr
  chain_ne_tree _ _ h := by cases h

private def family (extra : ℕ) : EncodingFamily Unit Bool Bool Bool (shape extra) where
  component _ :=
    { code := {fun _ => 0}
      incomparable := by
        intro x hx y hy hne
        have hx' : x = fun _ => 0 := Set.mem_singleton_iff.mp hx
        have hy' : y = fun _ => 0 := Set.mem_singleton_iff.mp hy
        exact False.elim (hne (hx'.trans hy'.symm))
      encode _ _ r _ := if r then some ⟨fun _ => 0, Set.mem_singleton _⟩ else none }

private noncomputable def sampling : RetrySampling Bool := RetrySampling.iid 1 1

private def goodKeys (extra : ℕ) :=
  keys (hash extra) () (fun _ _ => false)
    (fun (_ : UpperPosition (shape extra)) (_ : Fin 1) => true)

private noncomputable def signGood (extra : ℕ) :=
  signWithCoins (hash extra) (family extra) sampling (goodKeys extra).2 0 true (fun _ => true)

example : (signGood 0).isSome = true := by decide
example : (signGood 1).isSome = true := by decide
example : (signGood 2).isSome = true := by decide

example : (signGood 0).all (verify (hash 0) (family 0) (goodKeys 0).1 0 true) = true := by decide
example : (signGood 1).all (verify (hash 1) (family 1) (goodKeys 1).1 0 true) = true := by decide
example : (signGood 2).all (verify (hash 2) (family 2) (goodKeys 2).1 0 true) = true := by decide

private def failedKeys :=
  keys (hash 2) () (fun _ _ => false)
    (fun (p : UpperPosition (shape 2)) (_ : Fin 1) => if p.val.1.1.val = 1 then false else true)

example : signWithCoins (hash 2) (family 2) sampling failedKeys.2 0 true
    (fun _ => true) = none := by
  decide

example : signWithCoins (hash 2) (family 2) sampling failedKeys.2 0 false
    (fun _ => true) = none := by
  decide

example : (signWithCoins (hash 0) (family 0) sampling (goodKeys 0).2 0 true
    (fun _ => false)).isNone = true := by decide

private def rawSignature (extra : ℕ) (bottomRandomizer upperRandomizer : Bool) :
    Signature Bool Bool (shape extra) :=
  ⟨⟨bottomRandomizer, fun _ => false, Fin.elim0⟩,
    fun _ => ⟨upperRandomizer, fun _ => false, Fin.elim0⟩⟩

example : verify (hash 2) (family 2) (goodKeys 2).1 0 true (rawSignature 2 false true) =
    false := by decide

example : verify (hash 2) (family 2) (goodKeys 2).1 0 true (rawSignature 2 true false) =
    false := by decide

example : verify (hash 2) (family 2) ⟨false, ()⟩ 0 true (rawSignature 2 true true) = false := by
  decide

example (extra : ℕ) (ep : Epoch (shape extra)) (msg : Bool) (coins : sampling.bottom.Coins)
    (sig : Signature Bool Bool (shape extra))
    (h : signWithCoins (hash extra) (family extra) sampling (goodKeys extra).2 ep msg coins =
      some sig) :
    verify (hash extra) (family extra) (goodKeys extra).1 ep msg sig = true :=
  verify_signWithCoins _ _ _ _ _ (consistent_keys _ _ _ _) _ _ _ _ h

example : (PRFDerived.startGroup ⟨2, 16, 2, 58, by decide⟩ ⟨0, by decide⟩) =
    PRFDerived.startGroup ⟨2, 16, 2, 58, by decide⟩ ⟨1, by decide⟩ := by decide

example : PRFDerived.startHalf (S := ⟨2, 16, 2, 58, by decide⟩) ⟨0, by decide⟩ ≠
    PRFDerived.startHalf (S := ⟨2, 16, 2, 58, by decide⟩) ⟨1, by decide⟩ := by decide

private def pairShape : Shape := ⟨1, 0, 1, 2, by decide⟩
private def pairInterpretation : PRFDerived.Interpretation Unit Bool Bool (Bool × Bool) where
  publicParameter _ := ()
  chainStart := Prod.fst
  chainPair := id
  retryRandomizer := Prod.fst

example : PRFDerived.starts .pairedCounter (fun _ : OTSPosition pairShape => 1)
    (fun (_ : Unit) (_ : PRFDerived.Query Unit Bool Bool pairShape .pairedCounter (fun _ => 1)) =>
      (false, true)) pairInterpretation () () (bottomPosition pairShape 0)
      ⟨0, by decide⟩ = false := by decide

example : PRFDerived.starts .pairedCounter (fun _ : OTSPosition pairShape => 1)
    (fun (_ : Unit) (_ : PRFDerived.Query Unit Bool Bool pairShape .pairedCounter (fun _ => 1)) =>
      (false, true)) pairInterpretation () () (bottomPosition pairShape 0)
      ⟨1, by decide⟩ = true := by decide

example [DecidableEq (PRFDerived.Query Unit Bool Bool pairShape .pairedCounter (fun _ => 1))]
    (q : PRFDerived.Query Unit Bool Bool pairShape .pairedCounter (fun _ => 1))
    (cache : (PRFDerived.Query Unit Bool Bool pairShape .pairedCounter (fun _ => 1) →ₒ
      (Bool × Bool)).QueryCache) :
    ((PRFDerived.cachedQueryImpl (Sum.inr q)).run (cache.cacheQuery q (false, true))) =
      pure ((false, true), cache.cacheQuery q (false, true)) := by
  exact PRFDerived.cachedQuery_replay _ q (false, true) (by simp)

end GXMSS.Hypertree.Test

public meta section

run_cmd Lean.Elab.Command.liftTermElabM do
  GXMSS.Test.TrustAudit.check
    #[`HashSig.GXMSS.Hypertree.Scheme, `HashSig.GXMSS.Hypertree.Completeness,
      `HashSig.GXMSS.Hypertree.PRFDerivedScheme, `VCVio.CryptoFoundations.SyncSignatureCorrectness]
    #[(`GXMSS.Hypertree.verify_of_mem_support_sign, `HashSig.GXMSS.Hypertree.Completeness),
      (`GXMSS.Hypertree.PRFDerived.jointPairSampling, `HashSig.GXMSS.Hypertree.PRFDerivedScheme)]
    #[]
