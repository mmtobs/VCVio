/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerSource
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerGames
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainCollision
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerEncoding
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainGames

/-!
# Depth-one hypertree source and primitive observations

The source transports include raw keys, histories and complete Boolean winning measures.
Encoding uses an explicitly translated ordinary strategy. Chain problem, challenge, prefix and
guard maps do not assert full adaptive PRE or UD experiment correspondence.
-/
