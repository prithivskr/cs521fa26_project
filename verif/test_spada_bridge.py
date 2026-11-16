"""Integration tests use Rocq-extracted data, not hand-written Python kernels."""
import copy
import dataclasses
import json
from pathlib import Path
import unittest

import spada_bridge as bridge
from spada.syntax.spatial_ir import irnodes as ir
from spada.syntax.common.types import ScalarType

ROOT = Path(__file__).resolve().parent
GENERATED = ROOT / "generated-spada"


def load(name):
    return json.loads((GENERATED / f"{name}.json").read_text())


def tags(value):
    if isinstance(value, dict):
        if "$node" in value:
            yield value["$node"]
        for v in value.values():
            yield from tags(v)
    elif isinstance(value, list):
        for v in value:
            yield from tags(v)


class FullBridgeTests(unittest.TestCase):
    def test_every_public_ir_node_has_a_rocq_fixture(self):
        current = {name for name, cls in vars(ir).items()
                   if isinstance(cls, type) and cls.__module__ == ir.__name__
                   and issubclass(cls, ir.SpatialNode) and dataclasses.is_dataclass(cls)
                   and name not in {"SpatialNode", "Statement"}}
        self.assertEqual(current, bridge.NODE_NAMES)
        self.assertEqual(set(tags(load("fixtures"))) - {"$scalar", "$tuple", "$float_bits"}, current)
        values = bridge.decode(load("fixtures"))
        self.assertGreater(len(values), 30)

    def test_every_supported_scalar_is_represented(self):
        values = bridge.decode(load("fixtures"))
        self.assertEqual({v.name for v in values if isinstance(v, ScalarType)}, bridge.SCALARS)
        self.assertEqual(bridge.SCALARS, {t.name for t in ScalarType if t.name != "UNKNOWN"})

    def test_actual_csl_for_routed_and_async_programs(self):
        for name in ("ping", "multicast", "pipeline", "host"):
            with self.subTest(name=name):
                files = bridge.lower(bridge.decode(load(name)), disable_benchmarking=True)
                self.assertGreaterEqual(len(files), 2)
                self.assertTrue(all(f.code.strip() for f in files))
                self.assertTrue(any("@set_rectangle" in f.code for f in files))
                text = "\n".join(f.code for f in files)
                self.assertNotIn(".width = width", text)
                if name == "host":
                    self.assertIn(".MEMCPYH2D_1 = 0", text)
                    self.assertIn(".MEMCPYD2H_1 = 1", text)
                if name != "host":
                    self.assertIn("@set_color_config", text)
                    self.assertIn("fabout_dsd", text)
                    self.assertIn("fabin_dsd", text)

    def test_explicit_epochs_metaprogramming_and_bounded_host(self):
        for name in ("epochs", "meta", "bounded", "external"):
            with self.subTest(name=name):
                files = bridge.lower(bridge.decode(load(name)), disable_benchmarking=True)
                self.assertGreaterEqual(len(files), 2)
                self.assertNotIn(".width = width", "\n".join(f.code for f in files))

    def test_compiletime_argument_is_replaced_and_removed(self):
        kernel = bridge.decode(load("ping"))
        kernel.arguments.append(ir.KernelArgument(ScalarType.f32, ir.Identifier("scale", 0), compiletime=True))
        concrete = bridge.concretize(kernel, {"scale": 1.25})
        self.assertEqual(concrete.arguments, [])
        with self.assertRaisesRegex(ValueError, "unresolved"):
            bridge.concretize(kernel, {})

    def test_wse3_backend_in_fresh_processes(self):
        import subprocess
        import sys
        import tempfile
        for name in ("ping", "multicast", "pipeline", "epochs", "host", "bounded", "external", "meta"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                subprocess.run([sys.executable, str(ROOT / "spada_bridge.py"),
                                str(GENERATED / (name + ".json")), "--arch", "wse3",
                                "--output", directory], check=True, capture_output=True, text=True)
                self.assertTrue((Path(directory) / "layout.csl").exists())

    def test_proved_routing_variants_generate_the_same_csl(self):
        auto = bridge.lower(bridge.decode(load("ping")), disable_benchmarking=True)
        manual = bridge.lower(bridge.decode(load("manual-ping")), disable_benchmarking=True)
        self.assertEqual({f.filename: f.code for f in auto},
                         {f.filename: f.code.replace("rocq_ping_manual", "rocq_ping") for f in manual})

    def test_unknown_node_and_extra_fields_are_rejected(self):
        with self.assertRaises(ValueError):
            bridge.decode({"$node": "__import__", "name": "os"})
        invalid = copy.deepcopy(load("ping"))
        invalid["execute"] = "do not execute input"
        with self.assertRaises(ValueError):
            bridge.decode(invalid)
        invalid = {"$node": "Identifier", "name": "x", "version": True}
        with self.assertRaises(ValueError):
            bridge.decode(invalid)

    def test_float_bits_preserve_negative_zero(self):
        import math
        value = bridge.decode({"$node": "$float_bits", "type": "f32", "bits": 0x80000000})
        self.assertEqual(math.copysign(1.0, value), -1.0)
        with self.assertRaises(ValueError):
            bridge.decode({"$node": "$float_bits", "type": "f16", "bits": 65536})

    def test_parameter_defaults_are_concretized(self):
        kernel = bridge.decode(load("ping"))
        kernel.parameters = [ir.Parameter("N", 4)]
        concrete = bridge.concretize(kernel, {})
        self.assertEqual(concrete.parameters, [])
        kernel.parameters = [ir.Parameter("N")]
        with self.assertRaisesRegex(ValueError, "unresolved"):
            bridge.concretize(kernel, {})


if __name__ == "__main__":
    unittest.main()
