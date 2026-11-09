/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.SyncSignatureAlg

/-!
# Key-generation-averaged synchronized signature correctness

Correctness averaged over key generation differs from correctness for every generated key.
Fixed secret retry coins can produce a generated key that permanently fails at one epoch.
The per-key `SyncSignatureAlg.Complete` predicate retains its existing meaning.
-/

public section

namespace SyncSignatureAlg

open ENNReal

universe v

variable {m : Type → Type v} [Monad m] {M PK SK S E : Type}

/-- Generate a key, sign once, and observe actual verification, including returned failure. -/
@[expose] def averageCorrectnessExperiment (alg : SyncSignatureAlg m M PK SK S E)
    (ep : E) (msg : M) : m Bool := do
  let ks ← alg.keygen
  alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg

/-- Unnormalized successful-verification mass averaged over key generation. -/
@[expose] noncomputable def averageSuccessMass (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ep : E) (msg : M) : ℝ≥0∞ :=
  runtime.evalDist (alg.averageCorrectnessExperiment ep msg) {true}

/-- Keygen-averaged correctness; keygen/sign missing mass and returned rejection count as error. -/
@[expose] def AverageComplete (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) : Prop :=
  ∀ ep msg, 1 - δ ≤ alg.averageSuccessMass runtime ep msg

/-- Increasing the permitted averaged correctness error preserves the guarantee. -/
theorem AverageComplete.mono {alg : SyncSignatureAlg m M PK SK S E}
    {runtime : ProbCompRuntime m} {δ ε : ℝ≥0∞}
    (h : alg.AverageComplete runtime δ) (hle : δ ≤ ε) :
    alg.AverageComplete runtime ε :=
  fun ep msg => (tsub_le_tsub_left hle 1).trans (h ep msg)

/-- Averaged successful verification has mass at most one. -/
theorem averageSuccessMass_le_one (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ep : E) (msg : M) :
    alg.averageSuccessMass runtime ep msg ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ _)).trans
    (runtime.evalDist_apply_univ_le_one _)

/-- Zero averaged error is equivalent to unit success mass at every epoch and message. -/
theorem averageComplete_zero_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) :
    alg.AverageComplete runtime 0 ↔ ∀ ep msg,
      alg.averageSuccessMass runtime ep msg = 1 := by
  constructor
  · intro h ep msg
    exact le_antisymm (alg.averageSuccessMass_le_one runtime ep msg)
      (by simpa using h ep msg)
  · intro h ep msg
    simpa using le_of_eq (h ep msg).symm

end SyncSignatureAlg
