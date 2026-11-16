"""Differentially check the extracted arbitrary-precision reference arithmetic."""
import math
from pathlib import Path
import random
import struct
import subprocess
import unittest

ROOT = Path(__file__).resolve().parent


def unpack(width, bits):
    return struct.unpack({16: ">e", 32: ">f", 64: ">d"}[width], bits.to_bytes(width // 8, "big"))[0]


def pack(width, value):
    fmt = {16: ">e", 32: ">f", 64: ">d"}[width]
    try:
        raw = struct.pack(fmt, value)
    except OverflowError:
        raw = struct.pack(fmt, math.copysign(math.inf, value))
    return int.from_bytes(raw, "big")


class ArithmeticTests(unittest.TestCase):
    def test_ieee_against_host_reference(self):
        rng = random.Random(1811)
        lines, expected = [], []
        for width in (16, 32, 64):
            sign = 1 << (width - 1)
            frac = {16: 10, 32: 23, 64: 52}[width]
            inf = ((1 << ({16: 5, 32: 8, 64: 11}[width])) - 1) << frac
            cases = [0, sign, 1, sign | 1, inf - 1, inf, inf | sign, inf | 1,
                     pack(width, 1.0), pack(width, -1.0)]
            pairs = [(a, b) for a in cases for b in cases]
            pairs += [(rng.getrandbits(width), rng.getrandbits(width)) for _ in range(250)]
            for a, b in pairs:
                x, y = unpack(width, a), unpack(width, b)
                for name in ("add", "sub", "mul", "div"):
                    if name == "div" and y == 0:
                        if x == 0 or math.isnan(x):
                            z = math.nan
                        else:
                            z = math.copysign(math.inf, math.copysign(1, x) * math.copysign(1, y))
                    else:
                        z = {"add": lambda: x + y, "sub": lambda: x - y,
                             "mul": lambda: x * y, "div": lambda: x / y}[name]()
                    lines.append(f"f{width} {name} {a:x} {b:x}")
                    expected.append((width, pack(width, z)))
            # Check fused semantics independently with the host's correctly rounded fma.
            if hasattr(math, "fma"):
                for _ in range(200):
                    a, b, c = [rng.getrandbits(width) for _ in range(3)]
                    try:
                        z = math.fma(unpack(width, b), unpack(width, c), unpack(width, a))
                    except ValueError:
                        z = math.nan
                    except OverflowError:
                        z = math.copysign(math.inf, math.copysign(1.0, unpack(width, b)) *
                                          math.copysign(1.0, unpack(width, c)))
                    lines.append(f"f{width} fma {a:x} {b:x} {c:x}")
                    expected.append((width, pack(width, z)))
        run = subprocess.run([ROOT / "_build/numeric_driver"], input="\n".join(lines) + "\n",
                             text=True, capture_output=True, check=True, timeout=120)
        results = run.stdout.splitlines()
        self.assertEqual(len(expected), 4800 if hasattr(math, "fma") else 4200)
        self.assertEqual(len(results), len(expected))
        for line, actual, (width, target) in zip(lines, results, expected):
            self.assertNotEqual(actual, "none", line)
            actual = int(actual, 16)
            if math.isnan(unpack(width, target)):
                self.assertTrue(math.isnan(unpack(width, actual)), line)
            else:
                self.assertEqual(actual, target, line)


if __name__ == "__main__":
    unittest.main()
