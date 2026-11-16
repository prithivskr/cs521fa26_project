#!/usr/bin/env bash
# Compile and simulate existing, timing-enabled CSL. No source generation.
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
if [[ $# -ne 0 && $# -ne 2 ]]; then
  echo "Usage: bash $0 [BASELINE_CSL_DIRECTORY CACHED_CSL_DIRECTORY]" >&2
  exit 1
fi
baseline=${1:-"$root/generated-spada/summa-perf-baseline-wse3"}
cached=${2:-"$root/generated-spada/summa-perf-cached-wse3"}
for executable in cslc cs_python; do
  if ! command -v "$executable" >/dev/null 2>&1; then
    echo "Missing SDK executable: $executable" >&2
    exit 1
  fi
done
# Validate both source directories before starting either simulation.
for directory in "$baseline" "$cached"; do
  if [[ ! -f "$directory/layout.csl" ]]; then
    echo "Missing pre-generated CSL: $directory/layout.csl" >&2
    echo "Generate sources separately on the development host: make -C verif -f Full.mk summa-perf-sources" >&2
    exit 1
  fi
  if ! grep -q '"__benchmark_start"' "$directory/layout.csl" ||
     ! grep -q '"__benchmark_stop"' "$directory/layout.csl"; then
    echo "Timing exports are missing from $directory/layout.csl. Supply timing-enabled CSL." >&2
    exit 1
  fi
done
baseline=$(cd -- "$baseline" && pwd)
cached=$(cd -- "$cached" && pwd)
for variant in baseline cached; do
  if [[ "$variant" == baseline ]]; then dir="$baseline"; else dir="$cached"; fi
  cp "$root/benchmarks/run_summa.py" "$dir/run_summa.py"
  (
    cd "$dir"
    cslc --arch=wse3 layout.csl --fabric-dims=9,4 --fabric-offsets=4,1 \
      --memcpy --channels=1 -o out
    cs_python run_summa.py --name out --variant "$variant" --result result.json
  )
done
cd "$root"
cs_python benchmarks/compare_summa.py "$baseline/result.json" "$cached/result.json"
