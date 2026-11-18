#!/usr/bin/env python3
"""Scaling sweep for the receive-first 1xK chain reduction on the WSE-3 simulator.

For each K: extract JSON (Rocq -> OCaml chain_emit), lower with SpaDA, compile
with cslc, simulate with cs_python + run_chain.py. Records per-step wall times,
cycle_count, PASS/FAIL and the first failing step. Results are written after
every K to generated-spada/chain-sweep/results.{csv,json}.

Usage (from verif/):
  make -f Full.mk chain-emit
  .venv/bin/python benchmarks/chain_sweep.py                 # K = 4, 8, 16, ... until failure
  .venv/bin/python benchmarks/chain_sweep.py --ks 4 8 300    # explicit list (no early stop)
  .venv/bin/python benchmarks/chain_sweep.py --spada-root /path/to/patched/spada \
      --out generated-spada/chain-sweep-patched                # probe past a SpaDA bug
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
OUT = ROOT / 'generated-spada' / 'chain-sweep'
FIELDS = ['K', 'status', 'failed_step', 'emit_s', 'spada_s', 'cslc_s', 'sim_s',
          'cycle_count', 'sim_time_s', 'correct', 'error']


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
            # Container-hosted tools can outlive their wrapper's process group.
            subprocess.run(['pkill', '-9', '-f', ' '.join(cmd[1:4])], check=False)
            rc = 'timeout'
    return rc, round(time.monotonic() - start, 2)


def tail(log, n=6):
    try:
        text = re.sub(r'\x1b\[[0-9;]*m', '', Path(log).read_text(errors='replace'))
        lines = [l.rstrip() for l in text.splitlines() if l.strip() and not l.startswith('[INFO]')]
    except FileNotFoundError:
        return ''
    return ' | '.join(lines[-n:])[-800:]


def sweep_one(K, args):
    row = dict(K=K, status='FAIL', failed_step='', error='')
    work = OUT / f'K{K}'
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    json_path = work / f'chain-reduce-recvfirst-K{K}.json'
    csl_dir = work / 'csl'
    steps = [
        ('emit', [str(ROOT / '_build' / 'chain_emit'), str(work), str(K)], ROOT, args.emit_timeout),
        ('spada', [str(ROOT / '.venv' / 'bin' / 'python'), str(ROOT / 'spada_bridge.py'), str(json_path),
                   '--arch', 'wse3', '--output', str(csl_dir)], ROOT, args.spada_timeout),
        ('cslc', ['cslc', '--arch=wse3', 'layout.csl', f'--fabric-dims={K + 7},3',
                  '--fabric-offsets=4,1', '--memcpy', '--channels=1', '-o', 'out'],
         csl_dir, args.cslc_timeout),
        ('sim', ['cs_python', 'run_chain.py', '--name', 'out', '--K', str(K),
                 '--result', 'result.json']
         + ([] if args.trace else ['--suppress-trace'])
         + (['--threads', str(args.threads)] if args.threads else []), csl_dir, args.sim_timeout),
    ]
    for name, cmd, cwd, timeout in steps:
        if name == 'sim':
            shutil.copy(ROOT / 'benchmarks' / 'run_chain.py', csl_dir / 'run_chain.py')
        print(f'[K={K}] {name} ...', flush=True)
        rc, secs = run(cmd, cwd, timeout, work / f'{name}.log', args.env)
        row[f'{name}_s'] = secs
        print(f'[K={K}] {name} rc={rc} {secs}s', flush=True)
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
        row['correct'] = json.loads(res.read_text()).get('correct')
    if not row['failed_step'] and row.get('correct') is True:
        row['status'] = 'PASS'
    elif not row['failed_step']:
        row['failed_step'] = 'check'
        row['error'] = 'no result.json' if 'correct' not in row else 'result mismatch'
    if not args.keep:  # simulator output is large for big K
        shutil.rmtree(csl_dir / 'simfab_traces', ignore_errors=True)
    return row


def save(rows):
    (OUT / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')
    with open(OUT / 'results.csv', 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS, extrasaction='ignore')
        w.writeheader()
        w.writerows(rows)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--ks', type=int, nargs='*', help='explicit K values (default: doubling from --start)')
    p.add_argument('--start', type=int, default=4)
    p.add_argument('--max-k', type=int, default=1 << 14)
    p.add_argument('--emit-timeout', type=int, default=300)
    p.add_argument('--spada-timeout', type=int, default=1200)
    p.add_argument('--cslc-timeout', type=int, default=1200)
    p.add_argument('--sim-timeout', type=int, default=1200)
    p.add_argument('--spada-root', help='use this SpaDA checkout instead of ../spada (sets SPADA_ROOT)')
    p.add_argument('--out', help='results directory (default generated-spada/chain-sweep)')
    p.add_argument('--trace', action='store_true',
                   help='let the simulator write simfab_traces (off by default: 16 GB+ at K=512)')
    p.add_argument('--threads', type=int, help='simulator threads (SDK default: 5)')
    p.add_argument('--keep', action='store_true', help='keep simfab_traces')
    args = p.parse_args()
    global OUT
    if args.out:
        OUT = Path(args.out).resolve()
    args.env = dict(os.environ)
    if args.spada_root:
        args.env['SPADA_ROOT'] = str(Path(args.spada_root).resolve())
    if not (ROOT / '_build' / 'chain_emit').exists():
        sys.exit('missing _build/chain_emit: run make -f Full.mk chain-emit first')
    OUT.mkdir(parents=True, exist_ok=True)
    explicit = args.ks is not None and len(args.ks) > 0
    ks = args.ks if explicit else []
    if not explicit:
        k = args.start
        while k <= args.max_k:
            ks.append(k)
            k *= 2
    prev = OUT / 'results.json'
    rows = [r for r in (json.loads(prev.read_text()) if prev.exists() else []) if r['K'] not in ks]
    for K in ks:
        row = sweep_one(K, args)
        rows = sorted([r for r in rows if r['K'] != K] + [row], key=lambda r: r['K'])
        save(rows)
        print(json.dumps(row), flush=True)
        if row['status'] != 'PASS' and not explicit:
            print(f'Stopping at K={K}: {row["failed_step"]} failed', flush=True)
            break


if __name__ == '__main__':
    main()
