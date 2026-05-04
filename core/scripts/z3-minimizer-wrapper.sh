#!/usr/bin/env bash
# Thin shell wrapper that invokes the Python interactive z3 proxy.
# Required env vars:
#   PROOFPULSE_Z3_PATH  — path to real z3 binary
# Optional:
#   PROOFPULSE_PYTHON_PATH  — python interpreter (default: python)
#   PROOFPULSE_WRAPPER_LOG — path to debug log file

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PYTHON="${PROOFPULSE_PYTHON_PATH:-python}"
exec "$PYTHON" "$SCRIPT_DIR/z3-minimizer-wrapper.py" "$@"
