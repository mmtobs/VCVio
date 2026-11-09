# Arbitrary-depth generalized XMSS

The hypertree construction uses one public parameter and one hash across a positive number
of equal-height component trees. Its public namespace is `GXMSS.Hypertree`. Epochs remain
external to signatures, and one synchronized first-request history covers the entire forest.

## Construction and coordinates

Import `HashSig.GXMSS.Hypertree.Scheme` for the explicit-input construction and captured scheme.
`Coordinates` defines `Shape`, `Epoch`, `TreePosition`, `OTSPosition`, `UpperPosition`,
`positionAt`, `parent`, and `childTree`. Layers run from bottom to top. `HashInstance` gives
one global tweak domain and the existing component hash interface under `componentHash`.

With branching factor `b = 2^h` and digit radix `D = 2^w`, `treeCount` is the finite sum
`F = sum_(ell<d) b^(d-1-ell)`, `otsCount` is `L = b*F`, `upperCount` is
`U = F-1 = L-b^d`, and `chainCount` is `C = L*v*(D-1)`. The laws include depth one and
height zero without enumerating the forest.

`EncodingFamily` has full OTS coordinates and bottom-message/internal-digest fibres.
Every coordinate has its own incomparable code. There is no union-code incomparability
premise. Encoding collision security and the non-maximum-output property are separate
obligations; incomparability alone does not imply either.

`RetrySampling` captures a bottom and internal `Encoding.RetryPlan` and the actual coin
samplers. `RetrySampling.iid` uses independent finite attempt tuples. `RetrySampling.counter`
uses one uniform modular base and bounded consecutive offsets. Counter retries have their
own joint pushforward law and are not instances of the IID retry theorem.

`keys` assembles raw keys from a public parameter, the complete start table and fixed internal
coins. `certificateResult` computes the exact first-success/exhaustion metadata for a fixed
child root and tape. `certificate` retains its optional outcome. `signWithCoins` combines one
fresh bottom tape with the fixed internal tapes; `sign` supplies that bottom tape, and
`scheme` also captures parameterless key generation. A fixed failed internal certificate
therefore prevents every full signing request that passes through it from succeeding.

`recoverThrough`, `recoverRoot` and `verify` apply to arbitrary signature data. Verification
re-encodes each message and recovered child digest, completes chains, uses leaf-first paths,
and compares the recovered top root.

## Correctness

Import `HashSig.GXMSS.Hypertree.Completeness`. `verify_of_mem_support_sign` proves that every
successful returned signature verifies for consistent raw keys. It does not discard failure
or assert uniqueness of valid signatures.

`average_complete` proves keygen-averaged correctness from the actual per-kind retry failure
bounds. `average_complete_iid` derives the error
`delta_bottom^K_bottom + (d-1)*delta_internal^K_internal` from one-attempt error bounds.
`SyncSignatureAlg.AverageComplete` is defined separately in `SyncSignatureCorrectness`;
the existing per-generated-key `Complete` predicate is unchanged.

## Shared-key derivation

Import `HashSig.GXMSS.Hypertree.PRFDerivedScheme`. `PRFDerived.Query` is indexed by the actual
full-response layout: IID has individual starts and bounded per-attempt requests;
`pairedCounter` has start-group requests and a single base request per coordinate/message.
Both halves of a paired start response use the same request label. `Interpretation` decodes
complete responses, and `RetryInterpretation` supplies the finite coins of the selected plans.

`PRFDerived.keys`, `coreSecretKey`, `sign`, `keygen` and `scheme` use one original evaluator key
for the entire forest. `keys_snd` identifies the retained key exactly. Its distribution is
the supplied PRF key generator's distribution; no uniform derived seed is assumed.
`jointPairSampling` proves joint pair sampling from a bijective full-response decoder.
`cachedQueryImpl` uses a persistent cache of full responses in the ideal oracle, and
`cachedQuery_replay` preserves the complete stored response on repeats.

## Global security and the shared PRF hop

Import `HashSig.GXMSS.Security.Hypertree.Unforgeability` for
`GXMSS.Hypertree.Unforgeability.strong_unforgeability_reduction_bound` and its adjacent
`strongUnforgeabilityBound`. The displayed right-hand side is the sum of the four actual
collision advantages and the original-domain chain advantages with coefficients `C` and
`C*(D-1)`. The ordinary theorem is in the same file. The hypotheses include positive chain
count and width, the actual pathwise signing-query bound, and explicit fibrewise
`Family.NoMaximumOutput`. Two distinct codewords at each coordinate imply the last property;
shape positivity and incomparability alone do not.

The inspectable `Security/Hypertree/Reductions` directory contains the six named adversaries.
`TargetCounts` proves the actual chain and combined forest ledger lengths `C` and
`C+F*(2*b-1)`, their safe caps, accepted prefixes and global tweak separation.
`TargetRegistration` executes the authoritative hash games: registration has no public-seed
argument, and extraction after seed revelation returns the second input at the registered
first input's index.

`ForestWitnesses` partitions the actual native strong-forgery experiment. `Interaction` keeps
full consumed failures and the private bottom attempts, even when an upper certificate makes
the full signature fail. `ChainContinuation` recomputes roots, ancestor messages and fixed
retry results from each changed endpoint table. `ChainMass` supplies whole adaptive filtered
continuation laws. The generic splice, source-mass and telescope kernels live once under
`Security/Auxiliary`; the old complete/interval public endpoints specialize those helpers.

`FamilyEncoding` uses one mixed transcript, full coordinates and each fibre's own retry
plan. The eager record cap is `qs+U`. Its exact strategy-dependent collision advantage stays
explicit; neither incomparability nor correlated counter sampling implies it is small.
`EncodingAcceptedOutput` provides the ordinary IID accepted-output transport kernel.
`FamilyEncodingAcceptedOutput` supplies the mixed strategy-indexed native hash challenge:
it returns a selected randomizer or exhaustion and retains full consumed-coordinate records.
Its `AcceptedBridge` requires decoder injectivity only on each coordinate's accepted outputs.
Actual successful `family.value` equations in the invariant establish acceptance of both
compared digests. `HashRetry` transports the complete fixed-coin first-success result,
including attempt count and consumed prefix.

The direct and PRF files also expose `strong_unforgeability_reduction_bound_hashEncoding`
and `hashEncodingStrongUnforgeabilityBound`. They replace the encoding advantage using that
proved bridge, with no additional loss. The native hash primitive uses the captured retry
strategies. For counters it is distinct from IID SM-DT-rTCR; no hardness implication between
these primitives is asserted. Neither advantage is assumed small.

Import `HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability` for
`GXMSS.Hypertree.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound` and its
adjacent `strongUnforgeabilityBound`. This adds exactly one named PRF advantage to the direct
six-term bound. The security-layer `SamplingLaws` has local seed, start, bottom-coin and
internal-coin pushforward laws. Grouped starts require the joint two-start law. These local
laws prove the complete ideal interaction correspondence with one persistent full-response
cache. The real correspondence uses the actual retained evaluator key and its key generator.

The `randgenPRFReduction_query_bound` theorem in the `PRFDerivedQueryBounds` module
bounds the executed reduction.
The eager IID cap is `1+L*v+U*K_internal+qs*K_bottom`. The grouped cap is
`1+L*ceil(v/2)+U+qs`, including a base request for a zero-budget family. Public hash trial
work is separate. No running-time bound is asserted. The existing complete scheme's
three-query-family, three-law public theorem remains unchanged.

## Depth-one compatibility coverage

Import `HashSig.GXMSS.Hypertree.SingleLayer` for explicit epoch, coordinate, message, raw-key
and signature equivalences, root/path/verifier equations and IID signing/key-generation laws.
Import `HashSig.GXMSS.Security.Hypertree.SingleLayer` for actual enriched-source transports,
regular/strong Boolean measures and advantages, and the primitive observations.

The named Merkle, encoding, same-message chain, chain-cut and PRE reductions have complete
Boolean experiment and advantage transports to the established complete-tree reductions on
`adversaryToOrdinary`. `chainUDExperiment_single` preserves each authoritative UD world;
`chainUDAdvantage_single` preserves their advantage. The encoding correspondence uses the
same signing-query bound as the security theorem and compares the actual historical named
reduction, not only an unrelated translated strategy.

`SingleLayerChainGames` proves the joint spliced IID retry/filtered-history law. A killed native
filter returns fixed uniform-query answers while the ordinary filter keeps sampling. Their
optional forgery/history observations agree; raw killed-branch forgeries and operational costs
are not identified. `SingleLayerChainInvariant` retains each attempt's actual shared coin,
history coverage and unique consumed epoch. `SingleLayerChainObservation` and the cut lemmas
identify the current references and selected observation without assuming honest endpoints.
`SingleLayerChainExperiments` then proves full PRE and both UD experiment laws. The PRE proof
explicitly preserves accidental canonical-fallback wins and their returned Boolean mass.

`SingleLayerBound` proves `strongUnforgeabilityBound_single`, identifying all six named
advantages and sharp coefficients. `strongUnforgeabilityBound_eq_interval_full` recovers the sharp full-range
interval right-hand side. `strong_unforgeability_relaxed_complete` gives the established
complete-tree power-of-two relaxation separately. All these laws use actual game observations;
coefficient rewrites alone do not substitute for primitive experiment transport.

## Review and evidence limits

The focused consumers under `HashSigTest/GXMSS/Hypertree` include independent coordinate
canaries, successful/failing construction controls, correlated retry controls and kernel
origin/body/transitive-axiom audits. The
[public import consumer](../../HashSigTest/GXMSS/Hypertree/PublicAPI.lean) applies construction
and correctness endpoints through ordinary public imports.

The clean early construction checkpoint is qualified for functional transports only. A final
candidate's exact source, independent reviews, completed and missing checks, and depth-one
transport coverage belong in its accompanying human guide and consumer handoff. Read those
source-bound records before reuse. Compilation and agent review do not establish concrete hash
or PRF hardness, ROM/QROM security, serialization correctness or running-time bounds.
