#!/usr/bin/env python3
"""Decode Rocq's data-only AST directly into SpaDA objects and lower to CSL.

No source parser, eval, exec, import names from input, or generated Python code.
The backend is trusted: this adapter does not extend Rocq's compiler theorem.
"""
from __future__ import annotations

import argparse
import copy
import re
import dataclasses
import json
import os
from pathlib import Path
import struct
import sys
from typing import get_args, get_origin, get_type_hints, Union, Literal
import types

# Prefer the sibling checkout over an unrelated globally installed SpaDA.
SPADA_ROOT = Path(__file__).resolve().parents[1] / "spada"
sys.path.insert(0, str(SPADA_ROOT))
from spada.syntax.spatial_ir import irnodes as ir
from spada.syntax.common.types import ScalarType

# Every public concrete Spatial IR dataclass; base/visitor classes are excluded.
NODE_NAMES = frozenset({
    "ConstantLiteral", "Parameter", "Identifier", "StreamType", "ArrayType",
    "TypedIdentifier", "UnaryOperator", "BinaryOperator", "TernaryOperator",
    "MultiplyAccumulateOperator", "ArraySlice", "Expression", "RangeExpression",
    "SubgridExpression", "FieldDeclaration", "PlaceBlock", "RoutingHop",
    "RoutingDeclaration", "RelativeStreamDeclaration", "MulticastRangeStreamDeclaration",
    "ExternStreamDeclaration", "StreamDeclaration", "DataflowBlock", "Completion",
    "SendStatement", "ReceiveStatement", "ReceiveGenerator", "CloseStatement",
    "ForeachStatement", "MapStatement", "ForStatement", "AsyncBlock",
    "AwaitCompletionStatement", "AssignmentStatement", "AwaitAllStatement",
    "ComputeBlock", "MetaForBlock", "Phase", "KernelArgument", "Kernel",
})
SCALARS = frozenset({"i8", "i16", "i32", "u8", "u16", "u32", "f16", "f32", "f64", "bool"})


def decode(value):
    if value is None or type(value) in (str, int, bool):
        return value
    if isinstance(value, list):
        return [decode(v) for v in value]
    if not isinstance(value, dict) or "$node" not in value:
        raise ValueError("expected a tagged IR object")
    tag = value["$node"]
    fields = {k: v for k, v in value.items() if k != "$node"}
    if tag == "$scalar":
        if set(fields) != {"name"} or fields["name"] not in SCALARS:
            raise ValueError("unsupported scalar type")
        return ScalarType[fields["name"]]
    if tag == "$tuple":
        if set(fields) != {"items"} or not isinstance(fields["items"], list):
            raise ValueError("invalid tuple")
        return tuple(decode(v) for v in fields["items"])
    if tag == "$float_bits":
        if set(fields) != {"type", "bits"} or fields["type"] not in {"f16", "f32", "f64"}:
            raise ValueError("invalid floating literal")
        width, fmt = {"f16": (16, ">e"), "f32": (32, ">f"), "f64": (64, ">d")}[fields["type"]]
        bits = fields["bits"]
        if type(bits) is not int or not 0 <= bits < 2**width:
            raise ValueError("floating bit pattern out of range")
        return struct.unpack(fmt, bits.to_bytes(width // 8, "big"))[0]
    if tag not in NODE_NAMES:
        raise ValueError(f"unknown IR node: {tag!r}")
    cls = getattr(ir, tag)
    if tag == "AwaitAllStatement":
        if fields:
            raise ValueError("awaitall has no fields")
        return cls()
    spec = {f.name: f for f in dataclasses.fields(cls) if f.init}
    unknown = set(fields) - spec.keys()
    missing = {k for k, f in spec.items()
               if f.default is dataclasses.MISSING and f.default_factory is dataclasses.MISSING} - fields.keys()
    if unknown or missing:
        raise ValueError(f"invalid fields for {tag}: unknown={unknown}, missing={missing}")
    decoded = {k: decode(v) for k, v in fields.items()}
    if tag in {"UnaryOperator", "BinaryOperator"}:
        # These dataclasses call their outdated operator whitelist in __init__.
        # Validate all fields and the complete grammar whitelist below instead.
        result = object.__new__(cls)
        for key, field in spec.items():
            setattr(result, key, decoded.get(key, field.default))
    else:
        result = cls(**decoded)
    validate_types(result)
    # The parser supports these operators, but this checkout's node.validate
    # whitelists predate them. Keep all its other validation rules.
    if isinstance(result, ir.UnaryOperator):
        if result.op not in {"+", "-", "not", "~"}:
            raise ValueError("unknown unary operator")
    elif isinstance(result, ir.BinaryOperator):
        if result.op not in {"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=",
                             "<<", ">>", "&", "|", "^", "and", "or", "**"}:
            raise ValueError("unknown binary operator")
    else:
        result.validate()
    return result


def matches(value, annotation):
    origin = get_origin(annotation)
    args = get_args(annotation)
    if origin in (Union, types.UnionType):
        return any(matches(value, a) for a in args)
    if origin is Literal:
        return any(type(value) is type(a) and value == a for a in args)
    if origin is list:
        return isinstance(value, list) and all(matches(v, args[0]) for v in value)
    if origin is tuple:
        return (isinstance(value, tuple) and len(value) == len(args)
                and all(matches(v, a) for v, a in zip(value, args)))
    if annotation in (int, bool, str, float):
        return type(value) is annotation
    return isinstance(value, annotation)


def validate_types(node):
    hints = get_type_hints(type(node))
    for f in dataclasses.fields(node):
        if (isinstance(node, ir.ConstantLiteral) and f.name == "value"
                and node.dtype == ScalarType.bool and type(node.value) is bool):
            continue
        if f.init and not matches(getattr(node, f.name), hints[f.name]):
            raise ValueError(f"invalid type for {type(node).__name__}.{f.name}")


def concretize(kernel, parameters):
    from spada.syntax.spatial_ir import passes
    kernel = copy.deepcopy(kernel)
    parameter_names = {p.name for p in kernel.parameters}
    compile_args = {a.identifier.name: a.dtype for a in kernel.arguments if a.compiletime}
    unknown = set(parameters) - parameter_names - compile_args.keys()
    if unknown:
        raise ValueError(f"unknown compile-time settings: {sorted(unknown)}")
    defaults = {p.name: p.value for p in kernel.parameters if p.value is not None}
    defaults.update(parameters)
    unresolved = (parameter_names | compile_args.keys()) - defaults.keys()
    if unresolved:
        raise ValueError(f"unresolved parameters: {sorted(unresolved)}")
    if any(type(defaults[name]) is not int for name in parameter_names):
        raise ValueError("kernel parameters must be integers")
    for name, dtype in compile_args.items():
        if not isinstance(dtype, ScalarType):
            raise ValueError(f"compile-time argument {name} must be scalar")
    kernel.arguments = [a for a in kernel.arguments if not a.compiletime]
    kernel = passes.concretize_parameters(kernel, **{k: defaults[k] for k in parameter_names})

    class BindCompileArguments(ir.NodeTransformer):
        def visit_Identifier(self, node):
            if node.name in compile_args and node.version == 0:
                dtype = compile_args[node.name]
                value = defaults[node.name]
                if dtype in (ScalarType.f16, ScalarType.f32, ScalarType.f64):
                    value = float(value)
                elif dtype == ScalarType.bool:
                    value = bool(value)
                elif type(value) is not int:
                    raise ValueError(f"integer argument {node.name} requires an integer")
                return ir.ConstantLiteral(value, dtype)
            return node

    kernel = BindCompileArguments().visit(kernel)

    class BindParameters(ir.NodeTransformer):
        def visit_Parameter(self, node):
            value = defaults.get(node.name, node.value)
            if value is None:
                raise ValueError(f"unresolved expression parameter: {node.name}")
            return ir.ConstantLiteral(value, ScalarType.i32)

    kernel = BindParameters().visit(kernel)
    return passes.constexpr_propagation(kernel)


def lower(kernel, parameters=None, **options):
    from spada.lowering.spatial_ir_to_csl import lower_spatial_ir_to_csl, canonicalize_kernel
    concrete = concretize(kernel, parameters or {})
    interface = copy.deepcopy(concrete.arguments)
    # Recover the exact identifiers that phase/metaprogram canonicalization will
    # give explicit external streams, without mutating the actual input.
    normalized_interface = canonicalize_kernel(copy.deepcopy(concrete))
    seen = {(a.identifier.name, a.identifier.version, a.readonly, a.writeonly) for a in interface}
    for node in normalized_interface.walk():
        if isinstance(node, ir.StreamDeclaration) and isinstance(node.stream, ir.ExternStreamDeclaration):
            incoming = node.stream.direction == "in"
            key = (node.stream_name.name, node.stream_name.version, incoming, not incoming)
            if key not in seen:
                interface.append(ir.KernelArgument(node.dtype, node.stream_name,
                                                   readonly=incoming, writeonly=not incoming))
                seen.add(key)
    from spada.syntax.csl import dsd_ops
    previous_dsd_setting = dsd_ops.DISABLE_DSD
    try:
        dsd_ops.DISABLE_DSD = options.get("disable_dsd", False)
        files = lower_spatial_ir_to_csl(concrete, **options)
    finally:
        dsd_ops.DISABLE_DSD = previous_dsd_setting
    return complete_memcpy_layout(files, interface)


def complete_memcpy_layout(files, interface):
    """Fill two missing pieces of this checkout's streaming layout prologue.

    SpaDA removes stream arguments before writing the prologue and emits free
    width/height names. Recover the logical rectangle and external colors from
    its own generated declarations. Use SDK's one-based memcpy channel names.
    Do not alter PE code, route configurations, or scheduling.
    """
    from spada.syntax.csl.statements import name_to_csl
    layout = next(f for f in files if f.filename == "layout.csl")
    if ".width = width" not in layout.code:
        return files
    rectangle = re.search(r"@set_rectangle\((\d+),\s*(\d+)\)", layout.code)
    if rectangle is None:
        raise ValueError("backend layout has no concrete rectangle")
    width, height = rectangle.groups()
    settings = [f"  .width = {width}", f"  .height = {height}"]
    pe_text = "\n".join(f.code for f in files if f is not layout)
    channels = {"in": 0, "out": 0}
    for argument in interface:
        dtype = argument.dtype.base_type if isinstance(argument.dtype, ir.ArrayType) else argument.dtype
        if not isinstance(dtype, ir.StreamType) or dtype.buffer_size is not None:
            continue
        directions = (["in"] if argument.readonly else ["out"] if argument.writeonly else ["in", "out"])
        name = name_to_csl(argument.identifier)
        for direction in directions:
            colors = set(re.findall(r"const " + re.escape(name) +
                r"_color_" + direction + r": color = @get_color\((\d+)\)", pe_text))
            if not colors:
                continue  # Unused interfaces have no transfer tasks.
            if len(colors) != 1:
                raise ValueError(f"inconsistent external colors for {name}")
            channels[direction] += 1
            if channels[direction] > 4:
                raise ValueError("more than four host streams in one direction")
            key = "MEMCPYH2D" if direction == "in" else "MEMCPYD2H"
            settings.append(f"  .{key}_{channels[direction]} = {colors.pop()}")
    prologue = ('// Memcpy parameters completed by Rocq SpaDA adapter.\n'
                'const memcpy = @import_module("<memcpy/get_params>", .{\n' +
                ",\n".join(settings) + '\n});\n')
    _, sep, body = layout.code.partition("layout {")
    if not sep:
        raise ValueError("backend layout has no layout block")
    layout.code = prologue + sep + body
    return files


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, default=Path("generated-spada"))
    parser.add_argument("--arch", choices=("wse2", "wse3"), default="wse2")
    parser.add_argument("--param", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--benchmarking", action="store_true")
    parser.add_argument("--no-task-fusion", action="store_true")
    parser.add_argument("--no-copy-elision", action="store_true")
    parser.add_argument("--no-prune-memory", action="store_true")
    parser.add_argument("--no-dsd", action="store_true")
    parser.add_argument("--no-asynchronous", action="store_true")
    parser.add_argument("--no-task-id-recycling", action="store_true")
    parser.add_argument("--no-close-elision", action="store_true")
    parser.add_argument("--no-switching", action="store_true")
    args = parser.parse_args(argv)
    os.environ["WSE_ARCH"] = args.arch  # Must precede importing CSL modules.
    kernel = decode(json.loads(args.input.read_text()))
    if not isinstance(kernel, ir.Kernel):
        parser.error("input root must be a Kernel")
    if args.validate_only:
        print(f"validated {kernel.name}: {len(kernel.body)} top-level blocks")
        return
    parameters = {}
    for setting in args.param:
        key, sep, value = setting.partition("=")
        if not sep:
            parser.error("--param requires NAME=VALUE")
        try:
            parameters[key] = int(value)
        except ValueError:
            parameters[key] = float(value)
    files = lower(kernel, parameters,
                  disable_benchmarking=not args.benchmarking,
                  disable_asynchronous=args.no_asynchronous,
                  disable_dsd=args.no_dsd,
                  task_fusion=not args.no_task_fusion,
                  copy_elision=not args.no_copy_elision,
                  prune_memory=not args.no_prune_memory,
                  task_id_recycling=not args.no_task_id_recycling,
                  close_elision=not args.no_close_elision,
                  disable_switching=args.no_switching)
    args.output.mkdir(parents=True, exist_ok=True)
    for file in files:
        path = Path(file.filename)
        if path.name != file.filename or path.is_absolute():
            raise ValueError(f"unsafe backend filename: {file.filename}")
        (args.output / path).write_text(file.code)
    print(f"wrote {len(files)} CSL files to {args.output}")


if __name__ == "__main__":
    main()
