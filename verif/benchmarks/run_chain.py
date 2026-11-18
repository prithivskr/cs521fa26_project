#!/usr/bin/env python3
"""Run 1xK chain reduction in the simulator; compare bitwise to a0 + (a1 + (... + a[K-1]))."""
import argparse
import json
from pathlib import Path
import numpy as np
from cerebras.sdk.runtime.sdkruntimepybind import SdkRuntime, MemcpyDataType, MemcpyOrder


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--name', required=True, help='compiled output directory')
    parser.add_argument('--seed', type=int, default=521)
    parser.add_argument('--result', help='optional JSON results file')
    parser.add_argument('--K', type=int, default=4, help='PEs in the row (= vector length)')
    parser.add_argument('--suppress-trace', action='store_true',
                        help='do not write simfab_traces (they reach GBs for K >= 512)')
    parser.add_argument('--threads', type=int, help='simulator threads (SDK default: 5)')
    args = parser.parse_args()
    K = args.K
    assert K >= 2, 'K must be >= 2'
    rng = np.random.default_rng(args.seed)
    a = rng.uniform(-10, 10, (K, K)).astype(np.float32)
    # Values where association order changes the float32 result (needs K >= 4;
    # rows 0-3 / columns 0-3 carry the cancellation pattern, the rest is random).
    if K >= 4:
        a[0, 0], a[1, 0], a[2, 0], a[3, 0] = 1.0e8, -1.0e8, 3.25, 1.0
        a[0, 1], a[3, 1] = -3.0e38, -1.5e7
        a[1, 2], a[2, 2] = 1.0e-30, -7.5e20
        a[2, 3] = np.float32(1 / 3)
    expected = a[K - 1].copy()  # right-nested a0 + (a1 + (... + a[K-1])), float32
    for i in range(K - 2, -1, -1):
        expected = a[i] + expected
    assert expected.dtype == np.float32
    left_nested = a[0].copy()
    for i in range(1, K):
        left_nested = left_nested + a[i]
    if K >= 4:
        assert not np.array_equal(left_nested.view(np.uint32), expected.view(np.uint32))

    kwargs = {}
    if args.suppress_trace:
        kwargs['suppress_simfab_trace'] = True
    if args.threads:
        kwargs['simfab_numthreads'] = args.threads
    runtime = SdkRuntime(args.name, **kwargs)
    a_in_id, out_id = runtime.get_id('a_in'), runtime.get_id('out')
    runtime.load()
    runtime.run()
    try:
        runtime.memcpy_h2d(a_in_id, a.ravel(), 0, 0, K, 1, K,
            streaming=False, data_type=MemcpyDataType.MEMCPY_32BIT,
            order=MemcpyOrder.ROW_MAJOR, nonblock=False)
        runtime.launch('chain_reduce', nonblock=False)
        raw = np.zeros(K, dtype=np.uint32)
        runtime.memcpy_d2h(raw, out_id, 0, 0, 1, 1, K,
            streaming=False, data_type=MemcpyDataType.MEMCPY_32BIT,
            order=MemcpyOrder.ROW_MAJOR, nonblock=False)
    finally:
        runtime.stop()
    got = raw.view(np.float32)
    exp_bits = expected.view(np.uint32)
    ok = bool(np.array_equal(raw, exp_bits))
    result = dict(K=K, correct=ok, inputs=a.tolist() if K <= 16 else None, expected=expected.tolist(),
                  got=got.tolist(), expected_bits=[f'{w:08x}' for w in exp_bits],
                  got_bits=[f'{w:08x}' for w in raw],
                  left_nested_bits=[f'{w:08x}' for w in left_nested.view(np.uint32)])
    print(json.dumps(result, indent=2))
    if args.result:
        Path(args.result).write_text(json.dumps(result, indent=2) + '\n')
    print('PASS' if ok else 'FAIL')
    raise SystemExit(0 if ok else 1)


if __name__ == '__main__':
    main()
