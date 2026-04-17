#!/usr/bin/env bash
# Usage: ./scripts/bundle-viewer.sh <dfy-file> <output-dir>
# Bundles static viewer + pre-computed analysis into a deployable directory.
set -euo pipefail

DFY_FILE="${1:?Usage: bundle-viewer.sh <dfy-file> <output-dir>}"
OUT_DIR="${2:?Usage: bundle-viewer.sh <dfy-file> <output-dir>}"
DFY_DIR="$(dirname "$DFY_FILE")"

mkdir -p "$OUT_DIR"
cp src/index.html src/app.js src/styles.css src/spans_provider.js "$OUT_DIR/"
cp "$DFY_FILE" "$OUT_DIR/source_code.dfy"
cp "$DFY_DIR/prover_log.txt" "$OUT_DIR/prover_log.txt"

echo "Viewer bundle ready at $OUT_DIR/"
