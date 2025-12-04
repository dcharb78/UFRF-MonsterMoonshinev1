#!/bin/bash
# Verification script for Monster Moonshine UFRF proof

set -e

echo "🔍 Verifying Monster Moonshine UFRF Proof..."
echo ""

# Check Lean version
echo "1. Checking Lean version..."
lean --version
echo ""

# Build project
echo "2. Building project..."
lake build
echo ""

# Check for sorries
echo "3. Checking for sorries/admits..."
SORRIES=$(lake build 2>&1 | grep -i "sorry\|admit" | wc -l)
if [ "$SORRIES" -eq 0 ]; then
    echo "   ✓ No sorries found"
else
    echo "   ✗ Found $SORRIES sorries"
    exit 1
fi
echo ""

# Verify main files compile
echo "4. Verifying main files..."
lean --check lean/Monster_Moonshine.lean && echo "   ✓ Monster_Moonshine.lean"
lean --check lean/PhaseLog_Monoid.lean && echo "   ✓ PhaseLog_Monoid.lean"
echo ""

echo "✅ All verifications passed!"
