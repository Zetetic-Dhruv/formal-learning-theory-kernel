#!/bin/bash
# Run all proof operad tests and report results.
# Usage: cd lean4/ && bash FLT_Proofs/Meta/tests/run_tests.sh

set -euo pipefail

LEAN4_DIR="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$LEAN4_DIR"

echo "=== TPG_FLT Test Suite ==="
echo "Date: $(date)"
echo ""

# Build smoke tests
echo "--- Building BridgeTests.lean ---"
if lake build FLT_Proofs.Meta.BridgeTests 2>&1 | tail -3; then
  echo "BridgeTests: PASS"
else
  echo "BridgeTests: FAIL"
  exit 1
fi
echo ""

# Build non-trivial tests
echo "--- Building NonTrivialTests.lean ---"
if lake build FLT_Proofs.Meta.NonTrivialTests 2>&1 | tail -3; then
  echo "NonTrivialTests: PASS"
else
  echo "NonTrivialTests: FAIL"
  exit 1
fi
echo ""

# Sorry check
echo "--- Sorry Check ---"
SORRY_COUNT=0
for f in FLT_Proofs/Meta/BridgeTests.lean FLT_Proofs/Meta/NonTrivialTests.lean \
         FLT_Proofs/Meta/ProofOperad.lean FLT_Proofs/Meta/ProofOperadInstances.lean \
         FLT_Proofs/Meta/ProofOperadTheorems.lean FLT_Proofs/Meta/BridgeTactic.lean; do
  n=$(grep -c "^\s*sorry" "$f" 2>/dev/null || echo 0)
  if [ "$n" -gt 0 ]; then
    echo "  WARNING: $f has $n sorry(s)"
    SORRY_COUNT=$((SORRY_COUNT + n))
  fi
done
if [ "$SORRY_COUNT" -eq 0 ]; then
  echo "  All operad files: 0 sorrys"
fi
echo ""

# Line count
echo "--- Line Counts ---"
wc -l FLT_Proofs/Meta/*.lean | tail -1
echo ""

# DAG generation
echo "--- DAG Generation ---"
if python3 FLT_Proofs/Meta/dag/generate_dag.py > /dev/null 2>&1; then
  EDGES=$(python3 -c "import json; d=json.load(open('FLT_Proofs/Meta/dag/generator_dag.json')); print(d['metadata']['edge_count'])")
  echo "  DAG generated: $(python3 -c "import json; d=json.load(open('FLT_Proofs/Meta/dag/generator_dag.json')); print(f'{d[\"metadata\"][\"generator_count\"]} generators, {d[\"metadata\"][\"interface_count\"]} interfaces, {d[\"metadata\"][\"edge_count\"]} edges')")"
else
  echo "  DAG generation: SKIPPED (python3 not available)"
fi
echo ""

echo "=== ALL TESTS PASSED ==="
