#!/bin/bash
# Reproduce local verification pilot
# Run from the kernel repo root
set -euo pipefail

KERN="FLT_Proofs"
OUTDIR="test/verification/local_pilot"
mkdir -p "$OUTDIR"

echo "=== Step 1: Build ==="
lake build 2>&1 | tee "$OUTDIR/build_log.txt"

echo "=== Step 2: Sorry check ==="
SORRY_COUNT=$(grep -rn --include="*.lean" -E '^\s*sorry\s*$' "$KERN/" 2>/dev/null | wc -l | tr -d ' ')
echo "Sorry count: $SORRY_COUNT" | tee "$OUTDIR/sorry_count.txt"
if [ "$SORRY_COUNT" -gt 0 ]; then
  echo "FAIL: sorry detected"
  exit 1
fi

echo "=== Step 3: Red-team grep ==="
for pattern in '^\s*axiom\s' 'native_decide' '@\[implemented_by' '@\[extern' 'ofReduceBool' 'trustCompiler' '^\s*unsafe\s' '^\s*opaque\s'; do
  COUNT=$(grep -rn --include="*.lean" -E "$pattern" "$KERN/" 2>/dev/null | wc -l | tr -d ' ')
  echo "$pattern: $COUNT hits"
done | tee "$OUTDIR/red_team_grep.txt"

echo "=== Step 4: #print axioms ==="
cat > /tmp/PrintAxioms.lean << 'LEAN'
import FLT_Proofs.Theorem.PAC
import FLT_Proofs.Complexity.Compression
#print axioms fundamental_theorem
#print axioms fundamental_vc_compression_with_info
#print axioms vc_characterization
#print axioms sauer_shelah
#print axioms mwu_approx_minimax
#print axioms finite_support_vc_approx
#print axioms roundtrip_blockHyp_eq_rep
#print axioms vcdim_finite_imp_compression_with_info
#print axioms compression_with_info_imp_vcdim_finite
#print axioms pac_imp_vcdim_finite
#print axioms online_imp_pac
#print axioms fundamental_rademacher
#print axioms fundamental_vc_compression
#print axioms decodeWitnessXCoords_encode_eq
#print axioms decodeWitnessLabel_eq_on_encoded
LEAN
lake env lean /tmp/PrintAxioms.lean 2>&1 | grep "depends on axioms" | tee "$OUTDIR/print_axioms.txt"

echo "=== Step 5: lean4checker ==="
# Requires lean4checker built for matching toolchain
CHECKER="${LEAN4CHECKER:-lean4checker}"
LP="$(find .lake/packages -path '*/build/lib/lean' -type d | tr '\n' ':').lake/build/lib/lean"
MODULES=(
  FLT_Proofs.Complexity.Compression
  FLT_Proofs.Complexity.FiniteSupportUC
  FLT_Proofs.Complexity.Generalization
  FLT_Proofs.Complexity.Symmetrization
  FLT_Proofs.Complexity.Rademacher
  FLT_Proofs.Theorem.PAC
  FLT_Proofs.Theorem.Extended
  FLT_Proofs.Theorem.Separation
  FLT_Proofs.Theorem.Online
  FLT_Proofs.Theorem.PACBayes
  FLT_Proofs.Bridge
  FLT_Proofs.PureMath.ApproxMinimax
  FLT_Proofs.PureMath.FiniteVCApprox
)
for mod in "${MODULES[@]}"; do
  echo -n "$mod: "
  LEAN_PATH="$LP" "$CHECKER" --fresh "$mod" 2>&1 | grep -v "Searching\|Found" | tr -d '\n'
  echo " [exit $?]"
done | tee "$OUTDIR/lean4checker.txt"

echo "=== All checks complete ==="
