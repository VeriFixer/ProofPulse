#!/usr/bin/env bash
set -euo pipefail

if [ -z "${PROOFPULSE_Z3_PATH:-}" ]; then
  echo "error: PROOFPULSE_Z3_PATH not set" >&2; exit 2
fi
if [ -z "${PROOFPULSE_MINIMIZER_SCRIPT:-}" ]; then
  echo "error: PROOFPULSE_MINIMIZER_SCRIPT not set" >&2; exit 2
fi

TMPFILE=$(mktemp /tmp/z3-minimize-XXXXXX.smt2)
trap 'rm -f "$TMPFILE"' EXIT
cat > "$TMPFILE"
python3 "$PROOFPULSE_MINIMIZER_SCRIPT" "$TMPFILE" --z3 "$PROOFPULSE_Z3_PATH" --quiet
