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
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerChainExperiments
public import HashSig.GXMSS.Security.Hypertree.Auxiliary.SingleLayerBound

/-!
# Depth-one hypertree source and primitive observations

The source transports include raw keys, histories and complete Boolean winning measures.
The named collision, encoding, preimage and both undetectability experiments retain their
ordinary complete-tree observations. Sharp full-range interval bounds and the separate
complete-tree relaxation use those same named primitive advantages.
-/
