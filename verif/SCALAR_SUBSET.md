# Spatial kernels in Rocq

A self-contained embedded DSL inspired by Spada's placed fields and per-PE
compute blocks. It has executable semantics, kernel equivalence relations,
proved lowering to a small CSL AST, and an executable CSL source generator.
Only Rocq's standard library is needed. Tested with Rocq 9.1.1 and OCaml 5.4.0.

```sh
cd verif
make check             # compile proofs, then independently check .vo files
make emit              # extract compiler and write generated/*.csl
```

`make emit` additionally needs `ocamlc`. `emit.ml` only writes files; program
construction, validation, lowering, and rendering all run from extracted Rocq.
In Rocq, `Eval vm_compute in example_files.` also returns the source bundle.

## Writing programs

A kernel has a rectangular grid, a uniform placed `u32` buffer on every PE,
and a `compute : nat -> nat -> command` function. Coordinates and all program
parameters are ordinary Rocq values, evaluated at code generation time. A
placed array is a contiguous interval of buffer slots. Independent compute
regions can be expressed by branching on coordinates in that Rocq function.
The example uses slots 0–3 and 4–7 as input vectors, 8–11 as outputs, and slot
12 for a coordinate tag.

```coq
Definition vector_add : command :=
  for_range 0 4 (fun i =>
    Store (8 + i)%nat (Add (Load i) (Load (4 + i)%nat))).

Definition example : kernel :=
  {| width := 2; height := 2; slots := 12;
     compute := fun _ _ => vector_add |}.

Definition sources := compile_files example.
```

The primitive language contains `Skip`, `Store`, `Seq`, and `Repeat`.
`for_range start count body` builds a static indexed loop; `Repeat` repeats
the same body sequentially. Both lower to unrolled scalar CSL assignments.
Expressions contain literals, loads, addition, and multiplication. Values
use exact integer arithmetic reduced modulo 2^32 **at every operation**,
including literals and loads. No floating-point algebra assumptions are made.
All placed buffers must be initialized by the host before calling `run`;
repeated calls operate on the previous buffer contents.

`compile` rejects zero or oversized dimensions, empty or oversized buffers,
and every out-of-range read or write, including in nested/repeated bodies.
The current conservative limits are 32767 per grid dimension and 8192 buffer
words per PE. These are front-end limits, not a guarantee that a particular
wafer, memory configuration, or unrolled code size fits.

`compile_files` returns `option (list (string * string))`: a `layout.csl` and
one specialized `pe_X_Y.csl` per PE. The files export a host-readable/writable
`buffer : [*]u32` and a `run : fn()void`. The memcpy setup and command-stream
completion follow the installed SDK's `topic-01-arrays-and-pointers` example.
Compile `generated/layout.csl` with your SDK's normal architecture, fabric,
and memcpy settings. The layout describes the kernel's logical rectangle;
the compiler/runtime supplies its physical placement and memcpy infrastructure.

## Proving equivalence

`equivalent a b` equates the complete resulting local memories for every
initial memory. It is an extensional semantic relation, not syntax equality.
`kernel_equivalent` additionally equates grid/buffer shapes and all PE results.
`observationally_equivalent outputs` compares only named output slots, allowing
scratch contents to differ. No communication means PE scheduling cannot affect
these observations; memory outside the logical grid is unchanged.

Reusable lemmas include sequencing and loop congruence, sequencing
associativity, loop unrolling, and commutativity of addition in a store.
`kernel_congr` lifts local equivalence to grid equivalence. In `Examples.v`:

- Vector addition with reversed operands is equivalent across a 2×2 grid.
- A three-iteration loop equals its explicit unrolling.
- Removing a scratch buffer preserves output slot 2, including after lowering.
- Overflow wraps at 2^32; negative literals print as unsigned word literals.
- Invalid reads, invalid writes, and an empty grid are rejected.

The principal compiler theorems in `CSL.v` are:

```coq
lower_correct : forall c m,
  interpret (lower c) m = execute c m.

compile_correct : forall k p, compile k = Some p ->
  forall s x y, run_program p s x y = run k s x y.

compile_storage_safe : forall k p, compile k = Some p ->
  forall s x y j, (slots k <= j)%nat ->
    run_program p s x y j = s x y j.
```

`equivalence_preserved` and `observational_equivalence_preserved` transport
full-state and output-only source equivalence to lowered program equivalence. All proofs are complete: no `Admitted`, axioms, or
functional extensionality assumptions. `Print Assumptions` in the examples
reports that the main theorems are closed under the global context.

## Scope of the guarantee

The proved target is the executable scalar CSL **AST model**, with modular
`u32` operations. The source printer, OCaml extraction/runtime, SDK compiler,
memcpy library, and hardware are outside this proof. In particular, the proof
does not establish that parsing the emitted text recovers the target AST, or
verify CSL machine arithmetic against the model. Generated files were inspected
but could not be SDK-compiled in this environment: the installed SDK wrapper
requires Singularity, which is unavailable, and Docker is not running.

This is a synchronous PE-local subset, not an implementation of all Spada IR.
There are no inter-PE streams, routing/color allocation, completion handles,
asynchronous tasks, global barriers, dynamic loops/indices, or floats. `Seq`
orders work within each PE; it does not synchronize PEs. Adding streams should
introduce explicit queue/event semantics and observable execution traces before
proving routing or asynchronous transformations; modeling a send as a local
assignment would not justify those equivalences.

Files: `Spatial.v` defines syntax/semantics/equivalence; `CSL.v` defines the
backend and its proofs; `Examples.v` contains kernels and checked proofs;
`Extract.v` and `emit.ml` provide the optional file generation path.
