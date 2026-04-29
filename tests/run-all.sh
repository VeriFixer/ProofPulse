#!/usr/bin/env bash
# Run all ProofPulse test suites with clear separation.
set -o pipefail

BOLD='\033[1m'
DIM='\033[2m'
RESET='\033[0m'
GREEN='\033[32m'
RED='\033[31m'
CYAN='\033[36m'
GRAY='\033[90m'

PASS=0
FAIL=0
SKIP=0
SUITES=()

run_suite() {
  local name="$1"
  shift
  echo ""
  echo -e "${CYAN}${BOLD}━━━ ${name} ━━━${RESET}"
  echo -e "${DIM}$ $*${RESET}"
  echo ""

  if "$@"; then
    SUITES+=("${GREEN}✓${RESET} ${name}")
    ((PASS++))
  else
    SUITES+=("${RED}✗${RESET} ${name}")
    ((FAIL++))
  fi
}

skip_suite() {
  local name="$1"
  local reason="$2"
  SUITES+=("${DIM}⊘ ${name} — ${reason}${RESET}")
  ((SKIP++))
}

echo -e "${BOLD}${CYAN}ProofPulse — Full Test Suite${RESET}"
echo -e "${GRAY}$(date)${RESET}"

# 1. Unit tests (vitest)
run_suite "Unit tests" npx vitest --run --config vitest.config.ts tests/unit/

# 2. Property-based tests (vitest + fast-check)
run_suite "Property tests" npx vitest --run --config vitest.config.ts tests/property/

# 3. Integration tests (vitest)
run_suite "Integration tests" npx vitest --run --config vitest.config.ts tests/integration/

# 4. Server unit tests (node:test)
run_suite "Server tests" node --test tests/unit/web_viewer/server.test.js

# 5. Bundle tests (node:test)
run_suite "Bundle tests" node --test tests/unit/web_viewer/bundle-viewer.test.js

# 6. Evaluation tests
run_suite "Evaluation tests" npm test -w evaluation

# 7. Dafny regression suite (requires dafny)
if command -v dafny &>/dev/null; then
  run_suite "Dafny regression" npx tsx tests/harness/cli.ts
else
  skip_suite "Dafny regression" "dafny not in PATH"
fi

# Summary
TOTAL=$((PASS + FAIL + SKIP))
echo ""
echo -e "${GRAY}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${RESET}"
echo -e "${BOLD}Summary${RESET}  ${TOTAL} suites\n"
for s in "${SUITES[@]}"; do
  echo -e "  $s"
done
echo ""

if [ "$FAIL" -gt 0 ]; then
  echo -e "${RED}${BOLD}FAIL${RESET} — ${FAIL} suite(s) failed."
  exit 1
else
  echo -e "${GREEN}${BOLD}PASS${RESET} — all suites succeeded."
  exit 0
fi
