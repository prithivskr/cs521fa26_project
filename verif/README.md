# SpaDA Spatial IR in Rocq

The full embedded language is in `SpadaIR.v`. Kernels are ordinary Rocq values;
no Spatial-language parser or generated Python code is involved. It covers all
40 public concrete Spatial IR node classes and all 10 concrete scalar types in
the sibling SpaDA checkout. Schema coverage is checked against that checkout,
so adding an upstream node or scalar makes the coverage test fail.

The complete CSL path reuses SpaDA's backend, as requested. Rocq extracts a
**data-only AST**, and `spada_bridge.py` constructs SpaDA IR objects directly.
SpaDA performs geometry normalization, route/color allocation, DSD lowering,
completion/task generation, switch planning, and CSL rendering. This backend
and the adapter are trusted code, not a verified extension of the original
scalar compiler theorem.

## Build and generate CSL

Requirements: Rocq 9.1, OCaml, and Python with the packages in `requirements.txt`.
Python 3.13+ enables the independent host `math.fma` differential tests.

```sh
cd verif
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt

make check       # build all modules; independently recheck proof objects
make emit        # extract Rocq kernels, construct SpaDA IR, generate CSL
make full-test   # schema, backend, and extracted-arithmetic tests
```

The existing generated Makefile is extended through `Makefile.local`. It can
still be regenerated with `rocq makefile -f _CoqProject -o Makefile`.
The workspace-root `_CoqProject` supplies the same logical load path to Coq LSP
when the editor opens `cerebras/`; `verif/_CoqProject` supports opening `verif/`
directly. Restart the Coq language server after changing project settings.
`Full.mk` also works independently:

```sh
make -f Full.mk check
make -f Full.mk lower
make -f Full.mk test numeric-test
```

The default Python is `.venv/bin/python`; override with `PYTHON=/path/to/python`.
Generated files are under `generated-spada/`, with one directory per example.
For a particular Rocq-extracted AST:

```sh
.venv/bin/python spada_bridge.py generated-spada/pipeline.json \
  --arch wse3 --output generated-spada/pipeline-wse3
.venv/bin/python spada_bridge.py generated-spada/meta.json \
  --param N=8 --output generated-spada/meta-8
```

`--validate-only` checks the decoded schema. Normal lowering additionally runs
SpaDA's own canonicalization and validation. Hardware resource limits and
unsupported target combinations remain those of the selected SpaDA backend.
The adapter exposes its optimization switches through `--help`.

## Feature coverage

| SpaDA feature | Rocq representation and execution model |
|---|---|
| `i8/i16/i32`, `u8/u16/u32`, bool, `f16/f32/f64` | `scalar`; exact bit-pattern atoms and reference arithmetic |
| Literals, parameters, identifier versions | `literal`, `EParam`, `identifier`; defaults and specialization |
| Scalar/stream/array types, multidimensional shapes | `dtype`; tensors, broadcasting, indexed/sliced reads and writes |
| Unary, binary, comparison, shift, bitwise, logical, conditional expressions | `expression`; parameterized scalar operations and reference interpreter |
| Fused multiply-add | `FusedMultiplyAdd`; reference multiplication and addition before one rounding |
| Half-open ranges, strides, singleton ranges, subgrids | `Range`, `Grid`; coordinate and Cartesian iteration |
| Placed scalars/arrays and extern fields | `Place`, `Field`; phase-aware name resolution |
| Relative and multicast streams, relay offsets | `Relative`, `Multicast`; logical edge topology and multicast FIFO sends |
| External input/output streams | `ExternalInput`, `ExternalOutput`; labeled host input/output/EOF |
| Automatic/explicit routing hops and channels | `routing`; preserved in backend handoff; physical routing is trusted |
| Bounded/unbounded streams, explicit/implicit close | `Stream`, `Close`; queue bounds, EOF, endpoint epochs |
| Scalar/bulk send and receive | `Send`, `Receive`; asynchronous tasks and element-wise FIFO progress |
| Bounded and range-free streaming foreach | `Foreach`; per-element binding, bounded iteration and EOF termination |
| Map, sequential for, async blocks | `Map`, `For`, `Async`; spawned iterations, sequential control and joins |
| Completion handles, immediate await, await-all | `completion`, `Await`, `AwaitAll`; task-local handles and child completion |
| Multiple phases and phase-local fields/streams | `Phase`; distinct storage/stream names, local await/close at boundaries |
| Compile-time metaprogramming | `MetaFor`; environment-sensitive expansion, including generated phases |
| Scalar/stream-array arguments, read/write/compile-time flags | `argument`; backend interface lowering and compile-time binding |

`UNKNOWN` is SpaDA's internal inference placeholder, not a concrete scalar type.
The grammar's logical, bitwise, and power forms are represented as well as its
node validators' older operator list. The adapter independently validates that
complete operator whitelist. Floating remainder and floating exponentiation
currently have no operation in the **reference arithmetic** model and return
`None`; another `arithmetic` implementation can define them. The trusted backend
can also reject operations or combinations it does not implement. In particular,
representing `f64` does not promise native f64 instructions on the target.

The scope here is SpaDA's **Spatial IR**. Stencil frontends, source parsers,
placement research tools, and runtime launchers are separate upstream tools.

## Authoring within Rocq

`SpadaExamples.v` contains eight executable kernels. For example:

```coq
Import ListNotations Spada.
Definition coords := [coord "x"; coord "y"].
Definition grid := rectangle 2 1.
Definition east := StreamDecl (Stream F32 (Some (int 4))) (named "east")
  (Relative (int 1) (int 0) auto_route).

(* See ping for placed arrays and separate sender/receiver compute regions. *)
Definition data := export ping.
```

`SpadaExtract.v` extracts these values; `spada_emit.ml` only writes the resulting
JSON strings. No input can select Python imports or execute Python code.
The examples exercise point-to-point transfers, positive multicast, an async
multi-phase pipeline, unbounded host streams, explicit channel epochs and manual
hops, metaprogramming, multidimensional bounded host arguments, and explicit
external streams.

## Semantics and equivalence proofs

The formal model is independent of the trusted backend:

- `SpadaSemantics.v`: executable tensor expressions, typed assignment conversion,
  task spawning/joining, shared PE-local memory, completion handles, finite FIFO
  capacity/backpressure, multicast, bounds, close/EOF, and external observations.
- `SpadaArithmetic.v`: modular integers and an executable binary IEEE reference
  model with gradual underflow and round-to-nearest, ties-to-even. NaNs use a
  canonical result payload. Operations use arbitrary-precision Rocq integers;
  extraction does not substitute overflowing OCaml machine arithmetic.
- `SpadaElaboration.v`: placements, strided subgrids, parameters, metaprogramming,
  scoped name resolution, local phase boundaries, and initial task construction.
  Its environment supplies compile-time values; runtime scalar arguments belong
  in the initial PE memories. This interprets validated programs, rather than
  duplicating SpaDA's entire type/placement/protocol checker.
  Elaboration fuel limits nesting depth; failure returns `None`, without silently
  truncating a program. Initial memories and logical wire descriptions are supplied
  explicitly. `to_network` constructs FIFOs from wires; `wire_agrees` states their
  agreement with source geometry.
- `SpadaEquivalence.v`: observable finite traces, termination, deadlock, infinite
  reduction, and bisimulation proof rules. `bisimulation_total_sound` preserves
  all these observations. No deterministic scheduler or fairness is assumed.
- `SpadaProgramProofs.v`: checked elaboration, lexical shadowing, distinct epochs,
  slicing/broadcasting, typed conversion, semantic rewrites, and a full transition-
  semantics proof of f32 constant-folding program equivalence.

`expression_equivalent ops a b` quantifies over all input environments.
`assignment_rewrite` lifts it to assignment effects.
`assignment_program_equivalent` proves equivalence of complete isolated programs,
including stuck/terminating/diverging behavior, for arbitrary initial memories.
For concurrent transformations, exhibit a relation between machine states and
use `bisimulation_total_sound`. An observer can select exported buffers and ignore
private scratch, while host input/output remains visible in the trace.

`KernelEquivalence.kernel_equivalent` lifts the observation relation to elaborated
kernels, quantifying over initial memories, host queues, and a common logical
network. This form supports transformations that preserve topology. Comparing
changed topologies additionally requires a correspondence between the two logical
networks and their external edge names; this is not inferred automatically.

The arithmetic model is an explicit parameter: proofs may use the provided
reference or a different hardware-specific model. Never substitute real-number
associativity for floating-point behavior. The reference arithmetic has checked
edge-case examples and 4,800 differential cases against host IEEE operations and
`math.fma` in the tested Python environment. This is testing, not a proof of
conformance to the entire IEEE standard or to Cerebras' hardware modes.

The main equivalence and bisimulation proofs contain no `Admitted` or declared
axioms. `Print Assumptions` reports them closed under the global context.

## Proof boundary and validation

**No source-to-CSL correctness theorem is claimed for the full language.** The
complete path relies on SpaDA's compiler, as agreed. Extraction, the data adapter,
SpaDA, its optimizations, CSL rendering, the SDK, and hardware remain outside the
Rocq proof boundary. The earlier `Spatial.v`/`CSL.v` scalar subset and its lowering
proofs remain available; their theorem does not automatically extend to these
new modules.

The network semantics models logical communication. It does not certify physical
hop routing, colors, switches, collective channel reuse, or data-race freedom.
A proof using it must supply correctly matched logical wires and establish the
program's typing, initialization, race-freedom, and routing obligations. In
particular, `wire_agrees` checks geometric agreement, not completeness or physical
channel safety. Task completion waits for child tasks; phase boundaries wait and
close **locally**, without turning SpaDA phases into global barriers.

The adapter repairs concrete omissions in this checkout's streaming layout
prologue: free `width`/`height` names and lost external-stream memcpy parameters.
It recovers dimensions and colors from backend output, uses the SDK's one-based
memcpy stream names, and preserves PE code and on-chip route/task generation.
It also handles compile-time scalar arguments and restores SpaDA's mutable DSD
option between calls. These adapter changes are integration-tested, not proved.

Validation performed here:

- Rocq compilation and independent proof-object checking.
- Complete public-node and concrete-scalar schema coverage against the checkout.
- CSL generation for eight Rocq-authored kernels on WSE-2 and WSE-3.
- Rejection of malformed interchange data and unresolved compile-time settings.
- Extracted reference arithmetic differential tests, including fused operations.

CSL source generation was exercised; SDK compilation and hardware execution were
not available. The installed wrapper requires Singularity, and Docker is not
running. Generated sources therefore have not been certified by `cslc`.

The first implementation's design notes are preserved in `SCALAR_SUBSET.md`;
its original generation commands describe the earlier standalone Makefile.

## Cross-network refinement and communicating kernel proofs

`SpadaRefinement.v` adds `weak_certificate_sound`. A certificate can compare two
networks and two different output observers, permitting private scratch layouts
to change. Each source transition is matched by a target execution with the same
external event; silent source transitions may match zero or more silent target
transitions. Exit obligations preserve termination and deadlock with equal
observed outputs. Divergence preservation is a separate mandatory obligation,
so silent infinite loops cannot disappear through stuttering. Host edge names
must refer to the same public interface on both sides.

`bisimulation_infinite_execution` additionally preserves complete labelled
infinite executions for the existing strong bisimulation relation. This retains
communication labels, in addition to the earlier boolean divergence property.

`SpadaKernelProofs.v` connects certificates to source-kernel elaboration. Its
`deployment` requires successful elaboration, a checked finite wire table,
source-geometry agreement, and the actual elaborated initial state. Wire-table
checks reject duplicate edge IDs, zero capacities, missing endpoints, and
ambiguous receiver entries. Completeness, initialization, typing, races and
physical channel safety still require separate justification.

The module proves `communicating_kernels_equivalent` for the two-PE `ping`
kernel and a version with explicit hops and a channel. The proof holds for all
initial memories, queues and observers, conditional on both route selections
realizing the same logical FIFO network. It preserves every schedule's observable
behavior, including possible deadlock and divergence; it does not assert that
the kernel terminates. A concrete four-element FIFO of capacity one is supplied.
This example changes routing annotations; it does not demonstrate a topology-
changing optimization. The cross-network certificate rule supports such proofs
when their state/network correspondence is supplied.

Both kernels are extracted and handed to SpaDA. An integration test checks that
they generate identical CSL after normalizing the exported kernel name. All
new theorems are checked without admitted proofs or declared axioms. These
additions strengthen equivalence reasoning; they do not extend the trust
boundary to a verified SpaDA backend or complete static checker.

## Executable stream inference and Rocq routing

`SpadaDeployment.v` removes the need to hand-write logical wires for the supported
static deployment path:

```coq
compile_routes fuel ops compile_time_environment fifo_capacity
  available_colors separation_certificate kernel
```

It elaborates placements/metaprogramming, expands static loop indices, resolves
stream selectors, and collects send/receive uses. Relative and multicast uses
produce directed inter-PE FIFOs; external streams and bounded/unbounded stream
arguments produce host edges. Repeated operations share a FIFO. Bounds and
capacity are retained in the network. Unmatched uses, unresolved selectors,
ambiguous receivers, and zero capacities return `None`. `deployed_network` supplies
the inferred network to the existing small-step semantics; `start` constructs
its initial tasks. This is a partial deployment compiler for validated input,
not a complete type checker or proof of protocol correctness.

`SpadaRouting.v` implements XY Manhattan paths, checked explicit unit hops,
multicast path prefixes, and greedy allocation from a caller-supplied physical
color palette. The palette must exclude the target SDK's reserved colors. Routes
sharing PEs cannot share a color unless they are branches of the same multicast
or the supplied separation certificate permits reuse. An explicit logical channel
requires its routes to receive the same physical color. The allocator can reject
colorable graphs because it is greedy; it never silently invents extra colors.
Theorems establish membership in the palette and the checked pair constraints.
A separation predicate is an explicit assumption requiring independent semantic
justification; it is not inferred from phase numbers.

`SpadaRoutingCSL.v` merges route contributions into per-PE/color CSL configuration
statements. Multicast receivers can deliver to `RAMP` while forwarding on the
fabric. Multiple simultaneous receive ports are rejected. These snippets support
static routes; dynamic switch epochs and queue/task/DSD realization continue to
use the agreed trusted SpaDA backend. The reference planner does not replace or
force the backend's independent allocation.

`make emit` also produces `ping-routes.inc.csl` and
`multicast-routes.inc.csl` alongside complete backend-generated programs. These
are layout snippets using the example's palette, not standalone CSL programs or
patches to the backend-generated layout.

`SpadaRoutingExamples.v` checks point-to-point, multicast, host streaming,
bounded multidimensional arguments, external streams, and multi-phase inference.
It tests palette exhaustion, conflicting colors, invalid paths and unmatched
sends. `inferred_stream_kernel_equivalent` proves that automatically preparing
the two-PE transfer kernel preserves the earlier manual deployment's full
observable semantics, for arbitrary initial memories/queues. The proof uses the
same logical FIFO network; physical CSL correctness remains outside its scope.

The SDK-style SUMMA matrix multiplication example, accumulator optimization,
proofs, generated CSL and explicit proof boundaries are documented in
[SUMMA.md](SUMMA.md). Build it with `make -f Full.mk summa summa-test`.
