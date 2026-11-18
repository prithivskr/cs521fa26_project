#!/usr/bin/env python3
"""Scaling sweep for the P-stage SUMMA kernels (Summa.v) on the WSE-3 simulator.

For each (P, order): extract JSON (Rocq -> OCaml summa_emit), lower with SpaDA
(--arch wse3 --benchmarking), compile with cslc on a (P+7)x(P+2) fabric
(memcpy, 1 channel, offsets 4,1), simulate with cs_python + run_summa.py, and
check C against NumPy. Records per-step wall times, the simulator's
cycle_count (deterministic), max local PE cycles from the timestamp exports,
SpaDA's per-PE bytes/colour stats, the ELF memory footprint, and PASS/FAIL.
Results are rewritten after every run to OUT/results.{csv,json}.

Usage (from verif/):
  make -f Full.mk summa-emit
  .venv/bin/python benchmarks/summa_sweep.py                         # P = 2,3,4,6,8,12,16,... until failure
  .venv/bin/python benchmarks/summa_sweep.py --ps 4 --tile 8 8 8     # larger unrolled tile
  .venv/bin/python benchmarks/summa_sweep.py --spada-root /tmp/claude-1000/spada-patched \\
      --out generated-spada/summa-sweep-patched                      # patched SpaDA
"""
import argparse
import csv
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'generated-spada' / 'summa-sweep'
DEFAULT_PS = [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64]
FIELDS = ['P', 'order', 'Mt', 'Kt', 'Nt', 'compiler', 'status', 'failed_step',
          'emit_s', 'spada_s', 'cslc_s', 'sim_s', 'cycle_count', 'max_pe_cycles',
          'spada_max_bytes', 'spada_max_colors', 'elf_max_bytes', 'code_files',
          'json_bytes', 'sim_time_s', 'correct', 'max_abs_err', 'error']


def run(cmd, cwd, timeout, log, env=None):
    """Run cmd in its own process group; kill the whole group on timeout."""
    start = time.monotonic()
    with open(log, 'w') as fh:
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=fh, stderr=subprocess.STDOUT,
                                start_new_session=True, env=env)
        try:
            rc = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            rc = 'timeout'
    return rc, round(time.monotonic() - start, 2)


def tail(log, n=6):
    try:
        text = re.sub(r'\x1b\[[0-9;]*m', '', Path(log).read_text(errors='replace'))
        lines = [l.rstrip() for l in text.splitlines()
                 if l.strip() and not l.startswith('[INFO]') and 'deprecated' not in l
                 and "must be specified on the corresponding queue" not in l]
    except FileNotFoundError:
        return ''
    return ' | '.join(lines[-n:])[-800:]


def spada_stats(log):
    """Max bytes/PE and colours over SpaDA's 'Stats Px,y: N bytes/PE ... M colors' lines."""
    text = Path(log).read_text(errors='replace')
    b = [int(m) for m in re.findall(r'Stats P\d+,\d+: (\d+) bytes/PE', text)]
    c = [int(m) for m in re.findall(r'(\d+) colors\s*$', text, re.M)]
    return (max(b) if b else None), (max(c) if c else None)


def elf_footprint(bindir):
    """Max over PE ELFs of the end of the low (code+data+task table) memory region."""
    best = None
    for elf in Path(bindir).glob('out_*.elf'):
        out = subprocess.run(['size', '-A', str(elf)], capture_output=True, text=True).stdout
        end = 0
        for line in out.splitlines():
            parts = line.split()
            if len(parts) == 3 and parts[1].isdigit() and parts[2].isdigit():
                size, addr = int(parts[1]), int(parts[2])
                if parts[0] in ('.data.lo', '.text', '.data', '.bss', '.task_table'):
                    end = max(end, addr + size)
        best = end if best is None else max(best, end)
    return best


def sweep_one(P, order, tile, args):
    Mt, Kt, Nt = tile
    row = dict(P=P, order=order, Mt=Mt, Kt=Kt, Nt=Nt, compiler=args.compiler,
               status='FAIL', failed_step='', error='')
    work = OUT / f'{order}-P{P}-{Mt}x{Kt}x{Nt}'
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    json_path = work / f'summa-{order}-P{P}-{Mt}x{Kt}x{Nt}.json'
    csl_dir = work / 'csl'
    steps = [
        ('emit', [str(ROOT / '_build' / 'summa_emit'), str(work), str(P), str(Mt), str(Kt),
                  str(Nt), order], ROOT, args.emit_timeout),
        ('spada', [sys.executable, str(ROOT / 'spada_bridge.py'), str(json_path),
                   '--arch', 'wse3', '--benchmarking', '--output', str(csl_dir)],
         ROOT, args.spada_timeout),
        ('cslc', ['cslc', '--arch=wse3', 'layout.csl', f'--fabric-dims={P + 7},{P + 2}',
                  '--fabric-offsets=4,1', '--memcpy', '--channels=1', '-o', 'out'],
         csl_dir, args.cslc_timeout),
        ('sim', ['cs_python', 'run_summa.py', '--name', 'out', '--variant', order,
                 '--P', str(P), '--Mt', str(Mt), '--Kt', str(Kt), '--Nt', str(Nt),
                 '--result', 'result.json'], csl_dir, args.sim_timeout),
    ]
    for name, cmd, cwd, timeout in steps:
        if name == 'sim':
            shutil.copy(ROOT / 'benchmarks' / 'run_summa.py', csl_dir / 'run_summa.py')
        print(f'[P={P} {order}] {name} ...', flush=True)
        rc, secs = run(cmd, cwd, timeout, work / f'{name}.log', args.env)
        row[f'{name}_s'] = secs
        print(f'[P={P} {order}] {name} rc={rc} {secs}s', flush=True)
        if name == 'emit' and json_path.exists():
            row['json_bytes'] = json_path.stat().st_size
        if name == 'spada' and (work / 'spada.log').exists():
            row['spada_max_bytes'], row['spada_max_colors'] = spada_stats(work / 'spada.log')
            row['code_files'] = len(list(csl_dir.glob('code_*.csl')))
        if name == 'cslc' and rc == 0:
            row['elf_max_bytes'] = elf_footprint(csl_dir / 'out' / 'bin')
        if rc != 0:
            row['failed_step'] = name
            row['error'] = (f'timeout after {timeout}s' if rc == 'timeout'
                            else f'rc={rc}: ' + tail(work / f'{name}.log'))
            if name != 'sim':
                return row
    stats = csl_dir / 'sim_stats.json'
    if stats.exists():
        s = json.loads(stats.read_text())
        row['cycle_count'] = s.get('cycle_count')
        row['sim_time_s'] = round(s.get('sim_time', 0), 3)
    res = csl_dir / 'result.json'
    if res.exists():
        r = json.loads(res.read_text())
        row['correct'] = r.get('correct')
        row['max_pe_cycles'] = r.get('max_pe_cycles')
        row['max_abs_err'] = r.get('max_abs_err')
    if not row['failed_step'] and row.get('correct') is True:
        row['status'] = 'PASS'
    elif not row['failed_step']:
        row['failed_step'] = 'check'
        row['error'] = 'no result.json' if 'correct' not in row else 'result mismatch'
    if not args.keep:  # simulator traces and binaries are large for big P
        shutil.rmtree(csl_dir / 'simfab_traces', ignore_errors=True)
        shutil.rmtree(csl_dir / 'out', ignore_errors=True)
    return row


def key(r):
    return (r['Mt'], r['Kt'], r['Nt'], r['P'], r['order'])


def save(rows):
    (OUT / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')
    with open(OUT / 'results.csv', 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS, extrasaction='ignore')
        w.writeheader()
        w.writerows(rows)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--ps', type=int, nargs='*', help=f'explicit P values (default {DEFAULT_PS}, stop at first failure)')
    p.add_argument('--orders', nargs='*', default=['baseline', 'cached'], choices=['baseline', 'cached'])
    p.add_argument('--tile', type=int, nargs=3, default=[2, 3, 2], metavar=('MT', 'KT', 'NT'))
    p.add_argument('--emit-timeout', type=int, default=300)
    p.add_argument('--spada-timeout', type=int, default=1200)
    p.add_argument('--cslc-timeout', type=int, default=1200)
    p.add_argument('--sim-timeout', type=int, default=1200)
    p.add_argument('--spada-root', help='use this SpaDA checkout instead of ../spada (sets SPADA_ROOT)')
    p.add_argument('--out', help='results directory (default generated-spada/summa-sweep)')
    p.add_argument('--keep', action='store_true', help='keep simfab_traces and compiled binaries')
    args = p.parse_args()
    global OUT
    if args.out:
        OUT = Path(args.out).resolve()
    args.env = dict(os.environ)
    args.compiler = 'stock'
    if args.spada_root:
        args.env['SPADA_ROOT'] = str(Path(args.spada_root).resolve())
        args.compiler = 'patched:' + args.env['SPADA_ROOT']
    if not (ROOT / '_build' / 'summa_emit').exists():
        sys.exit('missing _build/summa_emit: run make -f Full.mk summa-emit first')
    OUT.mkdir(parents=True, exist_ok=True)
    explicit = bool(args.ps)
    ps = args.ps if explicit else DEFAULT_PS
    prev = OUT / 'results.json'
    rows = json.loads(prev.read_text()) if prev.exists() else []
    for P in ps:
        failed = False
        for order in args.orders:
            row = sweep_one(P, order, args.tile, args)
            rows = sorted([r for r in rows if key(r) != key(row)] + [row], key=key)
            save(rows)
            print(json.dumps(row), flush=True)
            failed |= row['status'] != 'PASS'
        if failed and not explicit:
            print(f'Stopping at P={P}', flush=True)
            break


if __name__ == '__main__':
    main()
