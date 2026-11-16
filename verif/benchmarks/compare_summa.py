"""Compare two completed simulator runs using only the Python standard library."""
import json
from pathlib import Path
import sys


def main():
    if len(sys.argv) != 3:
        raise SystemExit('Usage: compare_summa.py BASELINE_RESULT CACHED_RESULT')
    baseline, cached = [json.loads(Path(p).read_text()) for p in sys.argv[1:]]
    if not baseline['correct'] or not cached['correct']:
        raise SystemExit('Both results must pass correctness checks')
    a, b = baseline['max_pe_cycles'], cached['max_pe_cycles']
    print(f'Baseline max local PE cycles: {a}')
    print(f'Cached   max local PE cycles: {b}')
    if b:
        print(f'Baseline/cached cycle ratio: {a/b:.4f}x')


if __name__ == '__main__':
    main()
