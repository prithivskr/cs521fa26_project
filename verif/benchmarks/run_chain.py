#!/usr/bin/env python3
"""Run K=4 chain reduction in the simulator; compare bitwise to a0 + (a1 + (a2 + a3))."""
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
    args = parser.parse_args()
    K = 4
    rng = np.random.default_rng(args.seed)
    a = rng.uniform(-10, 10, (K, K)).astype(np.float32)
    # Values where association order changes the float32 result.
    a[0, 0], a[1, 0], a[2, 0], a[3, 0] = 1.0e8, -1.0e8, 3.25, 1.0
    a[0, 1], a[3, 1] = -3.0e38, -1.5e7
    a[1, 2], a[2, 2] = 1.0e-30, -7.5e20
    a[2, 3] = np.float32(1 / 3)
    expected = a[0] + (a[1] + (a[2] + a[3]))  # right-nested, all float32
    assert expected.dtype == np.float32
    left_nested = ((a[0] + a[1]) + a[2]) + a[3]
    assert not np.array_equal(left_nested.view(np.uint32), expected.view(np.uint32))

    runtime = SdkRuntime(args.name)
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
    result = dict(correct=ok, inputs=a.tolist(), expected=expected.tolist(),
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
