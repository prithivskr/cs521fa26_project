#!/usr/bin/env python3
"""Run one generated 2x2 SUMMA kernel in SdkRuntime's simulator."""
import argparse
import json
from pathlib import Path
import numpy as np
from cerebras.sdk.runtime.sdkruntimepybind import SdkRuntime, MemcpyDataType, MemcpyOrder


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--name', required=True, help='compiled output directory')
    parser.add_argument('--variant', required=True, choices=['baseline', 'cached'])
    parser.add_argument('--result', help='optional JSON results file')
    args = parser.parse_args()
    P, Mt, Kt, Nt = 2, 2, 3, 2
    rng = np.random.default_rng(7)
    A = rng.uniform(-1, 1, (P*Mt, P*Kt)).astype(np.float32)
    B = rng.uniform(-1, 1, (P*Kt, P*Nt)).astype(np.float32)
    a = A.reshape(P, Mt, P, Kt).transpose(0, 2, 3, 1).copy().ravel()
    b = B.reshape(P, Kt, P, Nt).transpose(0, 2, 3, 1).copy().ravel()
    runtime = SdkRuntime(args.name)
    ids = {s: runtime.get_id(s) for s in ['a', 'b', 'c', '__benchmark_start', '__benchmark_stop']}
    runtime.load()
    runtime.run()
    try:
        def upload(symbol, data, size):
            runtime.memcpy_h2d(ids[symbol], data, 0, 0, P, P, size,
                streaming=False, data_type=MemcpyDataType.MEMCPY_32BIT,
                order=MemcpyOrder.ROW_MAJOR, nonblock=False)
        upload('a', a, Mt*Kt)
        upload('b', b, Kt*Nt)
        upload('c', np.zeros(P*P*Mt*Nt, dtype=np.float32), Mt*Nt)
        runtime.launch('summa_' + args.variant, nonblock=False)
        c = np.zeros(P*P*Mt*Nt, dtype=np.uint32)
        runtime.memcpy_d2h(c, ids['c'], 0, 0, P, P, Mt*Nt,
            streaming=False, data_type=MemcpyDataType.MEMCPY_32BIT,
            order=MemcpyOrder.ROW_MAJOR, nonblock=False)
        C = c.view(np.float32).reshape(P, P, Nt, Mt).transpose(0, 3, 1, 2).reshape(P*Mt, P*Nt)
        np.testing.assert_allclose(C, A @ B, rtol=1e-5, atol=1e-6)
        timestamps = []
        for name in ['__benchmark_start', '__benchmark_stop']:
            words = np.zeros(P*P*3, dtype=np.uint32)
            runtime.memcpy_d2h(words, ids[name], 0, 0, P, P, 3,
                streaming=False, data_type=MemcpyDataType.MEMCPY_16BIT,
                order=MemcpyOrder.ROW_MAJOR, nonblock=False)
            words = words.reshape(P, P, 3).astype(np.uint64) & np.uint64(65535)
            timestamps.append(words[:, :, 0] | (words[:, :, 1] << np.uint64(16)) |
                              (words[:, :, 2] << np.uint64(32)))
        cycles = (timestamps[1] - timestamps[0]) & np.uint64((1 << 48)-1)
        result = dict(variant=args.variant, correct=True, pe_cycles=cycles.tolist(),
                      min_pe_cycles=int(cycles.min()), max_pe_cycles=int(cycles.max()),
                      mean_pe_cycles=float(cycles.mean()), matrix_shape=[4, 6, 4])
        print(json.dumps(result, indent=2))
        if args.result:
            Path(args.result).write_text(json.dumps(result, indent=2) + '\n')
    finally:
        runtime.stop()


if __name__ == '__main__':
    main()
