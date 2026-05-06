#!/usr/bin/env bash
# Thin shell wrapper that invokes the TypeScript interactive z3 proxy.
# Required env vars:
#   PROOFPULSE_Z3_PATH  — path to real z3 binary
# Optional:
#   PROOFPULSE_WRAPPER_LOG — path to debug log file

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DIST_DIR="$SCRIPT_DIR/../dist/minimization"
exec node "$DIST_DIR/wrapper.js" "$@"
