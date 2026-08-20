#!/bin/bash
# 8-way parallel sweep of C4-free connected cubic graphs on 24 vertices.
# Each part: geng (WSL) piped to the Python checker; results concatenated.
# Gate: Markstrom (2004) reports exactly 4 cubic graphs on 24 vertices with
# no C4 and no C8 -- our noC4noC8 total must be 4, counterexamples 0.
set -e
cd "$(dirname "$0")"
OUT=cubic24_parts
mkdir -p "$OUT"
for r in 0 1 2 3 4 5 6 7; do
  (
    wsl -d Ubuntu -- bash -c "export LD_LIBRARY_PATH=\$HOME/nauty-local/usr/lib/x86_64-linux-gnu:\$HOME/nauty-local/usr/lib; \$HOME/nauty-local/usr/bin/nauty-geng -c -d3 -D3 -f -q 24 $r/8" \
      | python check.py --stdin > "$OUT/part$r.txt" 2>&1
  ) &
done
wait
echo "=== parts ==="
cat "$OUT"/part*.txt
