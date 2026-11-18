#!/usr/bin/env bash
# Compile and simulate generated K=4 chain-reduction CSL (make -f Full.mk chain).
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
dir=${1:-"$root/generated-spada/chain-reduce-recvfirst-wse3"}
for executable in cslc cs_python; do
  if ! command -v "$executable" >/dev/null 2>&1; then
    echo "Missing SDK executable: $executable" >&2
    exit 1
  fi
done
if [[ ! -f "$dir/layout.csl" ]]; then
  echo "Missing CSL: $dir/layout.csl (run: make -f Full.mk chain)" >&2
  exit 1
fi
dir=$(cd -- "$dir" && pwd)
cp "$root/benchmarks/run_chain.py" "$dir/run_chain.py"
cd "$dir"
cslc --arch=wse3 layout.csl --fabric-dims=11,3 --fabric-offsets=4,1 \
  --memcpy --channels=1 -o out
timeout "${CHAIN_TIMEOUT:-600}" cs_python run_chain.py --name out --result result.json
