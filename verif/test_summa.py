"""Functional SUMMA harness; does not simulate CSL task scheduling/hardware."""
import copy
import math
from pathlib import Path
import random
import re
import struct
import unittest
import spada_bridge as bridge
import json
from spada.syntax.spatial_ir import irnodes as ir

ROOT = Path(__file__).resolve().parent


def f32(x):
    return struct.unpack(">f", struct.pack(">f", x))[0]


def interpret(kernel, original):
    memory = copy.deepcopy(original)
    for phase in (b for b in kernel.body if isinstance(b, ir.Phase)):
        messages = {}
        for block in phase.compute:
            x = block.subgrid.x_range.start.eval()
            y = block.subgrid.y_range.start.eval()
            for stmt in block.statements:
                if isinstance(stmt, ir.SendStatement):
                    decl = next(s for d in phase.dataflow for s in d.statements
                                if s.stream_name == stmt.stream_name)
                    dx, dy = decl.stream.dx.eval(), decl.stream.dy.eval()
                    messages[(x + dx, y + dy, stmt.stream_name.name)] = list(memory[x, y][stmt.local_array.name])
        for block in phase.compute:
            x, y = block.subgrid.x_range.start.eval(), block.subgrid.y_range.start.eval()
            m = memory[x, y]

            def address(node):
                if isinstance(node, ir.Identifier):
                    return node.name, 0
                return node.array.name, node.indices[0].eval()

            def value(expr):
                expr = expr.value
                if isinstance(expr, ir.MultiplyAccumulateOperator):
                    a, b, c = value(expr.a), value(expr.b), value(expr.c)
                    return f32(math.fma(b, c, a))
                name, index = address(expr)
                return m[name][index]

            for stmt in block.statements:
                if isinstance(stmt, ir.ReceiveStatement):
                    m[stmt.local_array.name] = messages[x, y, stmt.stream_name.name][:]
                elif isinstance(stmt, ir.AssignmentStatement):
                    name, index = address(stmt.destination)
                    m[name][index] = value(stmt.source)
    return memory


class SummaTests(unittest.TestCase):
    def kernels(self):
        return [bridge.decode(json.loads((ROOT / "generated-spada" / name).read_text()))
                for name in ("summa-baseline.json", "summa-cached.json")]

    def test_integer_gemm_and_nonzero_initial_c(self):
        rng = random.Random(17)
        for nonzero in (False, True):
            A = [[rng.randrange(-4, 5) for _ in range(6)] for _ in range(4)]
            B = [[rng.randrange(-4, 5) for _ in range(4)] for _ in range(6)]
            C = [[rng.randrange(-4, 5) if nonzero else 0 for _ in range(4)] for _ in range(4)]
            memory = {}
            for y in range(2):
                for x in range(2):
                    memory[x, y] = {
                        "a": [float(A[y*2+i][x*3+k]) for k in range(3) for i in range(2)],
                        "b": [float(B[y*3+k][x*2+j]) for j in range(2) for k in range(3)],
                        "c": [float(C[y*2+i][x*2+j]) for j in range(2) for i in range(2)],
                        "abuf": [0.0]*6, "bbuf": [0.0]*6, "acc": [0.0]}
            outputs = [interpret(k, memory) for k in self.kernels()]
            for x, y in memory:
                expected = [float(C[y*2+i][x*2+j] + sum(A[y*2+i][k] * B[k][x*2+j] for k in range(6)))
                            for j in range(2) for i in range(2)]
                self.assertEqual(outputs[0][x, y]["c"], expected)
                self.assertEqual(outputs[1][x, y]["c"], expected)

    def test_csl_generation_and_store_reduction(self):
        baseline, optimized = [bridge.lower(k, disable_benchmarking=True) for k in self.kernels()]
        for files, expected in ((baseline, 24), (optimized, 8)):
            pe_files = [f for f in files if f.filename != "layout.csl"]
            self.assertEqual(len(pe_files), 4)
            for file in pe_files:
                self.assertEqual(len(re.findall(r"^\s+c\[\d+\] =", file.code, re.M)), expected)


if __name__ == "__main__":
    unittest.main()
