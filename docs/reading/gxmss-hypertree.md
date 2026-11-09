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

The pure construction APIs do not themselves prove an executed PRF query bound or whole-game
real/ideal transport. Those security obligations must be qualified against their actual
reduction programs and local sampling laws.

## Review and evidence limits

The focused consumers under `HashSigTest/GXMSS/Hypertree` include independent coordinate
canaries, successful/failing construction controls, correlated retry controls and kernel
origin/body/transitive-axiom audits. `PublicAPI` applies construction/correctness endpoints
through ordinary public imports.

The early construction checkpoint is for functional transports. The direct six-reduction
security endpoint, PRF composition, all per-experiment depth-one transports and final
aggregate qualification must be checked separately before a security handoff. Compilation
and agent review do not establish concrete hash or PRF hardness, ROM/QROM security,
serialization correctness or running-time bounds.
