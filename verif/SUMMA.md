# SUMMA example and accumulator optimization

This example follows the computational structure of
`cs_sdk/csl-extras-202604101435-6-d2f7d96e/examples/benchmarks/gemm-collectives_2d`:
P stages on a P×P grid, row broadcasts of A from column stage, column broadcasts
of B from row stage, then local GEMM. Local tiles are column major.

`Summa.v` constructs complete Spatial IR kernels directly in Rocq. The concrete
example has P=2, Mt=2, Kt=3, Nt=2: a global (4×6) times (6×4) product. It exports
`a`, `b`, and `c` buffers on every PE. Initialize A/B from the corresponding
global matrix tiles. Initialize C to zero for C=AB, or supply an initial C for
C+=AB. Scratch fields `abuf`, `bbuf`, and `acc` are private.

Broadcasts are expanded into bounded point-to-point Spatial streams rather than
calls to the SDK collective library. Each stage waits for A and B locally before
computing. The kernel generator supports other dimensions. The concrete checked
certificate and local-emission proof use the dimensions above.

## Optimization

Baseline loop order: stage, k, j, i. Each FMA reads and writes C[i,j].

Cached loop order: stage, j, i; load C[i,j] into `acc`, perform k=0..Kt-1 FMAs,
then write C[i,j] once. Both retain the exact stage/k reduction order for each
output. No floating-point reassociation is used.

For the concrete example, per PE:

| Metric | Baseline | Cached |
|---|---:|---:|
| FMAs | 24 | 24 |
| C stores | 24 | 8 |
| Emitted PE storage | 112 bytes | 116 bytes |

The additional 4 bytes hold `acc`. This reduces C-array stores; it is not a
measured latency improvement. Scratch accesses, vectorization and register
allocation can affect performance. The SDK benchmark uses vector DSD FMAs;
these small kernels use statically unrolled scalar assignments. Unrolling also
avoids a dynamic indexed-assignment failure in this SpaDA checkout.

## What the proofs establish

`Summa.example_f32_equivalent` proves equality of all valid output elements in
the SUMMA functional semantics for arbitrary input tensors and initial C.
A checked certificate compares the *ordered* (stage,k) contribution traces for
each output. The generic theorem works for **any** FMA callback, so it applies
to the exact IEEE reference implementation without using real-number identities.
It also applies when the callback returns an error: both sides have the same
result/error behavior.

`SummaLocalProof.emitted_local_assignments_equivalent` separately interprets the
actual assignment/FMA lists produced by `local_compute`, including the `acc`
loads/stores. It proves equality of all four C outputs for every initial local
store, for each home/broadcast operand selection, and for any FMA callback.
`emitted_baseline_is_tile_gemm` and `emitted_cached_is_tile_gemm` identify those
results with the ordered three-term local dot products. These proofs exclude
scratch storage from observations.

**These are functional and local-emission proofs.** There is no completed
`weak_certificate` relating the two full `SpadaSemantics` asynchronous machines.
In particular, the example does not establish scheduler-level termination,
deadlock equivalence, or correct delivery of broadcasts in that model. The
functional proof assumes the usual SUMMA stage operands are delivered correctly.
The local interpreter is the same-typed assignment/FMA fragment, not a proved
refinement of the full typed tensor interpreter.

CSL lowering remains trusted. In this checkout scalar FMA IR prints as
`acc + a*b`; a proof that the CSL compiler contracts this into a fused operation
is absent. Therefore the IEEE corollary is a theorem about the reference DSL
semantics, not a bitwise CSL/hardware guarantee. SDK compilation, simulation and
hardware performance measurement were unavailable here (no Singularity or
running Docker daemon).

## Full-kernel proof (`SummaProof.v`)

`SummaProof.v` proves the lowered IR kernels themselves under the
hardware-agnostic semantics of `SpadaDataflow.v`, including the broadcasts.
For the example dimensions and both orders, `summa_correct` runs the whole
kernel phase by phase (`run_phased`) from arbitrary symbolic A, B, C and scratch
values, over any element type and any `fma`. Every PE finishes both phases and
its `c` equals the ordered SUMMA fold (`Summa.run`). `summa_baseline_cached`
follows, and both kernels are race-free (`summa_race_free`) and deadlock-free
under rendezvous (`summa_deadlock_free`). This closes the gap noted above for the
example: delivery of the stage operands is now proved, not assumed. CSL lowering
remains trusted.

## Reproduce

From `verif/`:

```sh
make -f Full.mk summa       # extract both kernels and generate complete CSL
make -f Full.mk summa-test  # check proof objects; run functional/codegen tests
```

The functional test executes the extracted Spatial IR ASTs with row/column
transfers, checks a deterministic matrix product with negative integer entries,
and checks nonzero initial C. The code-generation test counts actual C stores
in all four generated PE files. Python 3.13+ is required for `math.fma` in this
functional harness. It does not model asynchronous scheduling.

Generated programs are in `generated-spada/summa-baseline/` and
`generated-spada/summa-cached/`. JSON ASTs are adjacent. Use the existing bridge
with `--arch wse3` to select that backend. No source-language parser is used.

## Simulator performance

The simulator runner only compiles and executes existing CSL. It does not invoke
SpaDA, Rocq, make, a workspace virtualenv, or host Python. Its only executable
dependencies are the SDK's `cslc` and `cs_python`. The SDK Python supplies NumPy
and the runtime used by the host harness.

From the workspace root in a working SDK environment:

```sh
bash verif/benchmarks/summa_wse3.sh
```

It defaults to the pre-generated timing-enabled CSL in
`generated-spada/summa-perf-baseline-wse3/` and
`generated-spada/summa-perf-cached-wse3/`. To use copies elsewhere:

```sh
bash verif/benchmarks/summa_wse3.sh /path/to/baseline-csl /path/to/cached-csl
```

Both inputs must be the fixed 2×2-PE SUMMA example with timing exports. The runner
validates both directories before compilation. Each is compiled for WSE-3 with
a 9×4 fabric, offsets (4,1), memcpy enabled, and one memcpy channel. It launches a
fresh simulator runtime, initializes A/B/C, checks C against NumPy, and reads
3×u16 start/stop timestamps from every PE. Results are written to each input
CSL directory's `result.json`. Comparison uses `cs_python` with a standard-library
JSON reader; no host interpreter is involved.

The cycle ratio compares maximum **local** PE durations, not synchronized global
makespan or host simulation wall-clock time. This is the small proof instance
(24 FMAs per PE), so communication and timing overhead can dominate. The cached
variant is not guaranteed to be faster.

If sources change, regenerate them **separately on the development host**:

```sh
make -C verif -f Full.mk summa-perf-sources
```

That development-only target requires Rocq/OCaml and SpaDA's Python dependencies.
Copy the resulting CSL directories to the SDK host; the simulator runner does
not run that generation target automatically. Do not use the untimed directories
`summa-baseline-wse3/` and `summa-cached-wse3/` for cycle measurement.

The runner has been checked with stub SDK commands; actual SDK compilation and
simulation were unavailable locally. Repository SDK wrappers require Singularity;
alternatively use native SDK tools inside a working SDK/container environment.
