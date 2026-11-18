#!/usr/bin/env bash
# Compile and simulate generated 1xK chain-reduction CSL (make -f Full.mk chain).
# Usage: chain_wse3.sh [DIR [K]]   (K defaults to the memcpy width in DIR/layout.csl)
# memcpy (1 channel, offsets 4,1) needs a fabric of at least (K+7) x (1+2).
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
K=${2:-$(sed -n 's/^\.width = \([0-9]*\),$/\1/p' "$dir/layout.csl" | head -1)}
if [[ -z "$K" ]]; then
  echo "Cannot determine K from $dir/layout.csl; pass it as the second argument" >&2
  exit 1
fi
cp "$root/benchmarks/run_chain.py" "$dir/run_chain.py"
cd "$dir"
timeout "${CSLC_TIMEOUT:-1200}" cslc --arch=wse3 layout.csl \
  --fabric-dims=$((K + 7)),3 --fabric-offsets=4,1 \
  --memcpy --channels=1 -o out
timeout "${CHAIN_TIMEOUT:-600}" cs_python run_chain.py --name out --K "$K" --result result.json
