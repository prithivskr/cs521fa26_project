# Chain reduction under Kahn semantics

A standalone Rocq proof that the chain-reduction kernel from the SpaDA paper
computes an element-wise reduction, for every number of PEs `K >= 2` and every
vector length. It depends only on Rocq's standard library, not on `../verif`.

```sh
cd kahn
make check      # compile all files, then independently recheck the proofs
```

Tested with Rocq 9.1.1. No file has `Admitted` or axioms; `Print Assumptions`
reports every main theorem as closed under the global context.

## Files

| File | Role |
|---|---|
| `Spec.v` | **Specification.** `reduce`: the element-wise, right-nested sum of the PEs' vectors, over an arbitrary addition (`Plus`). `reduce_permutation`: with associative, commutative addition, the order of the vectors does not matter. |
| `Kahn.v` | **Framework.** A Kahn-process-network model of SpaDA kernels, generic in its stream, buffer and PE types: states, statements (`SendBuf`, `RecvBuf`, `Loop`), execution (`exec`, `run_pe`, `run_net`), and reusable lemmas for state updates and common loops (`foreach_add_forward`, `foreach_add`, `map_add`). |
| `ChainReduce.v` | **Kernel.** The paper's chain reduction (below) transcribed into the framework, statement by statement: streams, buffers, per-PE code (`process`), inputs and schedule. Both relay variants. |
| `ChainReduceProof.v` | **Proof.** The kernel meets the specification. |

`Spec.v` and `Kahn.v` know nothing about chain reduction, so a new kernel only
needs its own kernel and proof files.

## The kernel

From the SpaDA paper (its `N` in the east corner is read as `K`):

```
chain_reduce<K>(stream<f32>[K] readonly a_in, stream<f32>[1] writeonly out) {
  place i16 i, i16 j in [0:K, 0] { f32[K] a }
  phase { compute i32 i, i32 j in [0:K, 0] { await receive(a, a_in[i]) } }
  phase {
    dataflow i32 i, i32 j in [0:K, 0] {
      stream<f32> red  = relative_stream(-1, 0)
      stream<f32> blue = relative_stream(-1, 0)
    }
    compute i32 i, i32 j in [K-1, 0] {          // east corner
      await send(a, red if (K-1) % 2 == 0 else blue)
    }
    compute i32 i, i32 j in [1:K-1:2, 0] {      // odd PEs
      await foreach i32 k, f32 x in [0:K], receive(red) {
        a[k] = a[k] + x
        await send(a[k], blue)
      }
    }
    compute i32 i, i32 j in [2:K-1:2, 0] {      // even PEs
      await foreach i32 k, f32 x in [0:K], receive(blue) {
        a[k] = a[k] + x
        await send(a[k], red)
      }
    }
    compute i32 i, i32 j in [0, 0] {            // west corner (root)
      await foreach i32 k, f32 x in [0:K], receive(blue) { a[k] = a[k] + x }
      await send(a, out[i])
    }
  }
}
```

The proof also covers a **receive-first** variant, where each relay receives the
whole partial sum into a buffer `t`, adds `a[k] + t[k]`, then sends `a`. The
arithmetic is the same. It exists because SpaDA's switch planner mis-orders the
red/blue router positions for the original relay, which then stalls in the
Cerebras simulator; the variant runs and matches bit-exactly. The SpaDA IR
versions, CSL generation and simulator scripts are in `../verif`
(`ChainReduce.v`, `ChainReduceVariant.v`, `chain_bridge.py`,
`benchmarks/chain_wse3.sh`).

## The model

SpaDA's hardware-agnostic semantics (`irspec/docs/spatial/async.md` in [spcl/spada](https://github.com/spcl/spada))
requires that sends and receives on a stream line up one-to-one, that receives
block until data arrives, and that same-PE data races are undefined behaviour.
Such a program is a Kahn process network, so its result does not depend on the
schedule. `Kahn.v` therefore models:

- each stream edge as the list of values sent on it;
- each PE as a sequential program over its private memory;
- a run as the PEs executed one at a time, every producer before its consumers
  (PE `K-1` down to `0`). A receive that finds too little data fails.

## What is proved (`ChainReduceProof.v`)

| Theorem | Statement |
|---|---|
| `chain_reduce_correct` | For any addition, inputs and initial memories of the declared sizes, and either variant: the run completes, `out[0]` holds `a0 + (a1 + (... + a_{K-1}))` element-wise, and every other stream is fully consumed. No algebraic assumptions, so it holds for IEEE floats exactly. |
| `chain_reduce_any_order` | Assuming addition is associative and commutative (hypotheses, not axioms): the output equals the sum over any permutation of the PEs' vectors. |
| `chain_reduce_K1_deadlocks` | With `K = 1` the kernel gets stuck: PE 0 is both the east corner and the root, waiting on a PE 1 that does not exist. |
| `colors_match` | Every relay listens on the colour its east neighbour sends on (the paper's red/blue parity argument), for every `K`. |

## Trusted, not proved

1. **Kahn determinacy**: every interleaving produces this result. It relies on
   the SpaDA rules above; every statement in this kernel is awaited, so each PE
   is sequential and race-free.
2. **Transcription**: `process` is a hand transcription of the kernel above,
   written statement by statement with the source as comments.
3. **Bounded buffers**: deadlock freedom with finite FIFO capacity is argued,
   not proved. Data flows only westward and each PE receives before it sends,
   so no wait cycle exists.
4. **The compiler**: that SpaDA's CSL implements this semantics. The simulator
   shows it does not for the original kernel (see above).
